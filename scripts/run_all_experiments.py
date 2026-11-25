"""Generate all 16 canonical ALPHABETA-MONAD-CERT-1.0 certificates and 4 exact datasets.

Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.alphabeta_certifier import SCHEMA_VERSION, verify_certificate
from src.alphabeta_exact import (
    eval_exhaustive,
    eval_monadic_ab,
    ttt_monadic_ab,
    verify_optimal_play_def2,
)


def _write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def _lf(v: int) -> Dict[str, Any]:
    return {"kind": "leaf", "val": v}


def _mx(moves: List[int], children: List[Dict[str, Any]]) -> Dict[str, Any]:
    return {"kind": "max", "moves": moves, "children": children}


def _mn(moves: List[int], children: List[Dict[str, Any]]) -> Dict[str, Any]:
    return {"kind": "min", "moves": moves, "children": children}


def build_wiki_tree() -> Dict[str, Any]:
    """Exact 36-leaf example game tree from Escardo & Oliva Sec. 2.2, Fig. 1."""
    b00 = _mx([0, 1], [_mn([0, 1, 2], [_lf(5), _lf(6), _lf(6)]), _mn([0, 1, 2], [_lf(7), _lf(4), _lf(5)])])
    b01 = _mx([0, 1], [_mn([0, 1, 2], [_lf(3), _lf(3), _lf(3)]), _mn([0, 1, 2], [_lf(3), _lf(3), _lf(3)])])
    b10 = _mx([0, 1], [_mn([0, 1, 2], [_lf(6), _lf(6), _lf(6)]), _mn([0, 1, 2], [_lf(6), _lf(9), _lf(9)])])
    b11 = _mx([0, 1], [_mn([0, 1, 2], [_lf(7), _lf(7), _lf(7)]), _mn([0, 1, 2], [_lf(7), _lf(7), _lf(7)])])
    b20 = _mx([0, 1], [_mn([0, 1, 2], [_lf(5), _lf(5), _lf(5)]), _mn([0, 1, 2], [_lf(5), _lf(5), _lf(5)])])
    b21 = _mx([0, 1], [_mn([0, 1, 2], [_lf(9), _lf(9), _lf(9)]), _mn([0, 1, 2], [_lf(9), _lf(9), _lf(9)])])
    return _mx([0, 1, 2], [_mn([0, 1], [b00, b01]), _mn([0, 1], [b10, b11]), _mn([0, 1], [b20, b21])])


def build_asymmetric_history_tree() -> Dict[str, Any]:
    """History-dependent variable-branching, variable-depth game tree (Sec. 6.1)."""
    c0 = _mn([0, 1], [_lf(4), _mx([0, 1, 2], [_lf(2), _lf(8), _lf(1)])])
    c1 = _mn([0, 1, 2], [_mx([0, 1], [_lf(7), _lf(5)]), _lf(6), _mx([0, 1], [_lf(9), _lf(3)])])
    c2 = _mn([0, 1], [_lf(5), _lf(10)])
    return _mx([0, 1, 2], [c0, c1, c2])


def build_tied_pruning_trap_tree() -> Dict[str, Any]:
    """Adversarial tie-breaking tree (Sec. 5 p. 13): later pruned subgame yields tied bound 5."""
    # Move 0 has exact minimax value 5 via [0, 1]; move 1 has min([5, 2]) = 2,
    # where alpha=5 causes immediate cutoff at leaf 5 (returning bound 5!).
    # First-element pickMax MUST keep [0, 1] rather than displaced bound [1, 0]!
    return _mx(
        [0, 1, 2],
        [
            _mn([0, 1], [_lf(8), _lf(5)]),
            _mn([0, 1], [_lf(5), _lf(2)]),
            _mn([0, 1], [_lf(5), _lf(1)]),
        ],
    )


def build_best_order_depth4_tree() -> Dict[str, Any]:
    """Best-ordered binary depth-4 game tree (achieves near-sqrt(N) leaf pruning!)."""
    return _mx(
        [0, 1],
        [
            _mn(
                [0, 1],
                [
                    _mx([0, 1], [_mn([0, 1], [_lf(6), _lf(8)]), _mn([0, 1], [_lf(5), _lf(9)])]),
                    _mx([0, 1], [_mn([0, 1], [_lf(7), _lf(10)]), _mn([0, 1], [_lf(8), _lf(11)])]),
                ],
            ),
            _mn(
                [0, 1],
                [
                    _mx([0, 1], [_mn([0, 1], [_lf(4), _lf(7)]), _mn([0, 1], [_lf(3), _lf(9)])]),
                    _mx([0, 1], [_mn([0, 1], [_lf(2), _lf(5)]), _mn([0, 1], [_lf(1), _lf(6)])]),
                ],
            ),
        ],
    )


def _make_mode1_cert(cert_id: str, ref: str, tree: Dict[str, Any], alpha: int, beta: int) -> Dict[str, Any]:
    (ex_v, ex_p), ex_l = eval_exhaustive(tree)
    (ab_v, ab_p), tr = eval_monadic_ab(tree, alpha, beta)
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "fixed_tree_alphabeta_cert",
        "reference": ref,
        "payload": {
            "tree": tree,
            "alpha": alpha,
            "beta": beta,
            "claimed_exhaustive_val": ex_v,
            "claimed_exhaustive_play": ex_p,
            "claimed_exhaustive_leaves": ex_l,
            "claimed_ab_val": ab_v,
            "claimed_ab_play": ab_p,
            "claimed_ab_leaves": len(tr),
            "claimed_ab_trace": [[p, v] for p, v in tr],
        },
    }


def _make_mode2_cert(
    cert_id: str,
    ref: str,
    tree: Dict[str, Any],
    windows: List[Tuple[int, int]],
) -> Dict[str, Any]:
    (ex_v, ex_p), _ = eval_exhaustive(tree)
    checks = []
    for a, b in windows:
        (ab_v, ab_p), tr = eval_monadic_ab(tree, a, b)
        regime = "fail_low" if ex_v <= a else ("fail_high" if ex_v >= b else "exact_window")
        checks.append(
            {
                "alpha": a,
                "beta": b,
                "claimed_regime": regime,
                "claimed_ab_val": ab_v,
                "claimed_ab_play": ab_p,
                "claimed_ab_leaves": len(tr),
            }
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "tie_breaking_and_window_cert",
        "reference": ref,
        "payload": {
            "tree": tree,
            "claimed_exhaustive_val": ex_v,
            "claimed_exhaustive_play": ex_p,
            "window_checks": checks,
        },
    }


def _make_mode3_cert(cert_id: str, ref: str, tree: Dict[str, Any], alpha: int, beta: int) -> Dict[str, Any]:
    (ab_v, ab_p), _ = eval_monadic_ab(tree, alpha, beta)
    ok, ply_vals = verify_optimal_play_def2(tree, ab_p)
    assert ok
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "optimal_play_witness_cert",
        "reference": ref,
        "payload": {
            "tree": tree,
            "alpha": alpha,
            "beta": beta,
            "claimed_optimal_val": ab_v,
            "claimed_optimal_play": ab_p,
            "claimed_ply_values": ply_vals,
            "claimed_def2_optimal": True,
        },
    }


def _make_mode4_cert(
    cert_id: str,
    ref: str,
    prefix: List[int],
    alpha: int,
    beta: int,
    verify_ex: bool,
) -> Dict[str, Any]:
    ex_leaves = 1
    for i in range(2, 9 - len(prefix) + 1):
        ex_leaves *= i
    (ab_v, ab_p), ab_l = ttt_monadic_ab(prefix, alpha, beta)
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "history_dependent_ttt_cert",
        "reference": ref,
        "payload": {
            "prefix_moves": prefix,
            "alpha": alpha,
            "beta": beta,
            "verify_exhaustive_subgame": verify_ex,
            "claimed_exhaustive_leaves": ex_leaves,
            "claimed_ab_val": ab_v,
            "claimed_ab_play": ab_p,
            "claimed_ab_leaves": ab_l,
            "claimed_cor1b_exact": alpha < ab_v < beta,
        },
    }


def build_all_certificates() -> List[Tuple[str, Dict[str, Any]]]:
    wiki = build_wiki_tree()
    asym = build_asymmetric_history_tree()
    trap = build_tied_pruning_trap_tree()
    best4 = build_best_order_depth4_tree()

    certs: List[Tuple[str, Dict[str, Any]]] = []

    # --- Mode 1: Fixed Tree Monadic Alpha-Beta Traces (4 certs) ---
    certs.append((
        "m1_wiki_36leaf_to_18leaf",
        _make_mode1_cert("m1_wiki_36leaf_to_18leaf", "Escardo-Oliva arXiv:2611.32320 Sec. 2.2/3.3/5 (Wikipedia 36->18 tree)", wiki, -1000, 1000),
    ))
    certs.append((
        "m1_asymmetric_history_tree",
        _make_mode1_cert("m1_asymmetric_history_tree", "Escardo-Oliva arXiv:2611.32320 Sec. 6.1 (variable-depth history tree)", asym, -100, 100),
    ))
    certs.append((
        "m1_tied_pruning_trap_sec5",
        _make_mode1_cert("m1_tied_pruning_trap_sec5", "Escardo-Oliva arXiv:2611.32320 Sec. 5 (pickMax tie-breaking trap)", trap, -100, 100),
    ))
    certs.append((
        "m1_best_ordered_depth4_binary",
        _make_mode1_cert("m1_best_ordered_depth4_binary", "Escardo-Oliva arXiv:2611.32320 Sec. 3 (best-ordered depth-4 tree)", best4, -100, 100),
    ))

    # --- Mode 2: Theorem 1(i)-(iii) & Corollary 1(b) Window Stress Tests (4 certs) ---
    certs.append((
        "m2_wiki_aspiration_windows",
        _make_mode2_cert("m2_wiki_aspiration_windows", "Escardo-Oliva arXiv:2611.32320 Thm. 1 & Cor. 1(b) (wiki windows)", wiki, [(-1000, 1000), (5, 7), (6, 10), (0, 6), (3, 9)]),
    ))
    certs.append((
        "m2_tie_trap_boundary_windows",
        _make_mode2_cert("m2_tie_trap_boundary_windows", "Escardo-Oliva arXiv:2611.32320 Sec. 5 (tied-bound fail-low/high/exact)", trap, [(-10, 10), (4, 6), (5, 9), (1, 5)]),
    ))
    certs.append((
        "m2_asym_tree_windows",
        _make_mode2_cert("m2_asym_tree_windows", "Escardo-Oliva arXiv:2611.32320 Thm. 1 (asymmetric tree windows)", asym, [(-50, 50), (5, 7), (6, 9), (2, 6)]),
    ))
    certs.append((
        "m2_depth4_binary_windows",
        _make_mode2_cert("m2_depth4_binary_windows", "Escardo-Oliva arXiv:2611.32320 Cor. 1(a)-(b) (depth-4 windows)", best4, [(0, 20), (5, 7), (6, 12), (1, 6)]),
    ))

    # --- Mode 3: Definition 2 & Corollary 2 Optimal Play Witnesses (4 certs) ---
    certs.append((
        "m3_opt_play_wiki_1000",
        _make_mode3_cert("m3_opt_play_wiki_1000", "Escardo-Oliva arXiv:2611.32320 Sec. 5 Cor. 2 (wiki optimal play [1,0,0,0])", wiki, -1000, 1000),
    ))
    certs.append((
        "m3_opt_play_tied_trap",
        _make_mode3_cert("m3_opt_play_tied_trap", "Escardo-Oliva arXiv:2611.32320 Sec. 5 Def. 2 (tied-bound optimal play)", trap, 0, 10),
    ))
    certs.append((
        "m3_opt_play_asymmetric_tree",
        _make_mode3_cert("m3_opt_play_asymmetric_tree", "Escardo-Oliva arXiv:2611.32320 Sec. 6.1 Def. 2 (history-dependent play)", asym, 0, 20),
    ))
    certs.append((
        "m3_opt_play_best_depth4",
        _make_mode3_cert("m3_opt_play_best_depth4", "Escardo-Oliva arXiv:2611.32320 Cor. 2 (depth-4 optimal play)", best4, 0, 20),
    ))

    # --- Mode 4: Section 6.2 History-Dependent Tic-Tac-Toe (including full 9!=362,880 -> 9,335!) (4 certs) ---
    certs.append((
        "m4_ttt_full_root_362880_to_9335",
        _make_mode4_cert("m4_ttt_full_root_362880_to_9335", "Escardo-Oliva arXiv:2611.32320 Sec. 6.2 (full Tic-Tac-Toe 9!=362880->9335)", [], -1, 1, False),
    ))
    certs.append((
        "m4_ttt_subgame_ply3_draw",
        _make_mode4_cert("m4_ttt_subgame_ply3_draw", "Escardo-Oliva arXiv:2611.32320 Sec. 6.2 (Tic-Tac-Toe ply-3 [0,4,1] draw)", [0, 4, 1], -1, 1, True),
    ))
    certs.append((
        "m4_ttt_subgame_ply4_forced_draw",
        _make_mode4_cert("m4_ttt_subgame_ply4_forced_draw", "Escardo-Oliva arXiv:2611.32320 Sec. 6.2 (Tic-Tac-Toe ply-4 [0,4,1,2] Cor. 1(b))", [0, 4, 1, 2], -1, 1, True),
    ))
    certs.append((
        "m4_ttt_subgame_ply3_x_wins_wide",
        _make_mode4_cert("m4_ttt_subgame_ply3_x_wins_wide", "Escardo-Oliva arXiv:2611.32320 Sec. 6.2 (Tic-Tac-Toe [0,1,4] X win under (-2,2))", [0, 1, 4], -2, 2, True),
    ))

    assert len(certs) == 16
    return certs


def main() -> None:
    cert_dir = ROOT / "certificates"
    data_dir = ROOT / "data"
    cert_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    certs = build_all_certificates()
    replay_rows = []
    for name, cert in certs:
        _write_json(cert_dir / f"{name}.json", cert)
        t0 = time.perf_counter_ns()
        ok, msg, summary = verify_certificate(cert)
        dt_ns = time.perf_counter_ns() - t0
        if not ok:
            raise RuntimeError(f"Canonical cert {name} failed verification: {msg}")
        replay_rows.append(
            {
                "cert_id": name,
                "mode": cert["mode"],
                "ok": ok,
                "verify_ns": dt_ns,
                "summary": summary,
            }
        )
    _write_json(data_dir / "certificate_replay_summary.json", {"certificates": replay_rows})

    # Dataset 1: Tic-Tac-Toe pruning factor along Escardo & Oliva's optimal play [0,4,1,2,6,3,5,7,8] from ply 0..6
    opt_play = [0, 4, 1, 2, 6, 3, 5, 7, 8]
    exp1_rows = []
    for ply in range(0, 7):
        pref = opt_play[:ply]
        ex_l = 1
        for i in range(2, 9 - ply + 1):
            ex_l *= i
        (val, play), ab_l = ttt_monadic_ab(pref, -1, 1)
        exp1_rows.append(
            {
                "ply": ply,
                "prefix": pref,
                "exhaustive_leaves": ex_l,
                "ab_leaves": ab_l,
                "speedup_ratio": round(ex_l / ab_l, 3),
                "optimal_val": val,
                "optimal_play": play,
            }
        )
    _write_json(data_dir / "exp1_ttt_ply_pruning_curve.json", {"rows": exp1_rows})

    # Dataset 2: Wikipedia 36-leaf tree pruning across window widths centered at optimal value 6
    wiki = build_wiki_tree()
    exp2_rows = []
    for label, a, b in [
        ("(-1000,1000)", -1000, 1000),
        ("(0,12)", 0, 12),
        ("(3,9)", 3, 9),
        ("(5,7)", 5, 7),
        ("(6,10) fail-low", 6, 10),
        ("(0,6) fail-high", 0, 6),
    ]:
        (ab_v, ab_p), tr = eval_monadic_ab(wiki, a, b)
        exp2_rows.append(
            {
                "window": label,
                "alpha": a,
                "beta": b,
                "ab_val": ab_v,
                "ab_leaves": len(tr),
                "exhaustive_leaves": 36,
                "pruned_leaves": 36 - len(tr),
            }
        )
    _write_json(data_dir / "exp2_wiki_window_sensitivity.json", {"rows": exp2_rows})

    # Dataset 3: Comparison across all 4 Mode 1 benchmark game trees
    exp3_rows = [r["summary"] for r in replay_rows if r["mode"] == "fixed_tree_alphabeta_cert"]
    _write_json(data_dir / "exp3_tree_pruning_summary.json", {"rows": exp3_rows})

    total_ms = sum(r["verify_ns"] for r in replay_rows) / 1_000_000
    min_ms = min(r["verify_ns"] for r in replay_rows) / 1_000_000
    max_ms = max(r["verify_ns"] for r in replay_rows) / 1_000_000
    print(f"Generated & verified 16/16 canonical ALPHABETA-MONAD-CERT-1.0 certificates ({min_ms:.3f}-{max_ms:.3f} ms, total {total_ms:.2f} ms).")


if __name__ == "__main__":
    main()
