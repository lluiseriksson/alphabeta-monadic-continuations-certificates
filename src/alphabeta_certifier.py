"""Exact zero-floating-point four-mode certificate verifier for ALPHABETA-MONAD-CERT-1.0.

Verifies exact monadic continuation + reader alpha-beta pruning, Theorem 1 / Corollary 1(a)-(b)
window invariants, Definition 2 / Corollary 2 optimal plays, and Section 6.2 history-dependent
Tic-Tac-Toe pruning for:
  Martin Hotzel Escardo and Paulo Oliva, "Alpha-Beta Pruning via Monadic Continuations"
  (arXiv:2611.32320, Nov 24, 2026).

Strictly zero floating-point operations (uses int, bool, str, list exclusively).
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from src.alphabeta_exact import (
    eval_exhaustive,
    eval_monadic_ab,
    ttt_exhaustive,
    ttt_monadic_ab,
    verify_optimal_play_def2,
)

SCHEMA_VERSION = "ALPHABETA-MONAD-CERT-1.0"
MAX_BIT_LEN = 2048
MAX_JSON_DEPTH = 32
MAX_ID_LEN = 128

VALID_MODES = {
    "fixed_tree_alphabeta_cert",
    "tie_breaking_and_window_cert",
    "optimal_play_witness_cert",
    "history_dependent_ttt_cert",
}


class CertError(ValueError):
    """Raised when a certificate violates schema, typing, or mathematical invariants."""


def _int_fact(n: int) -> int:
    res = 1
    for i in range(2, n + 1):
        res *= i
    return res


def _assert_strict_json_types(obj: Any, path: str = "root", depth: int = 0) -> None:
    if depth > MAX_JSON_DEPTH:
        raise CertError(f"{path}: JSON nesting depth exceeds {MAX_JSON_DEPTH}")
    if obj is None or type(obj) in (bool, int, str):
        return
    if type(obj) is list:
        for i, item in enumerate(obj):
            _assert_strict_json_types(item, f"{path}[{i}]", depth + 1)
        return
    if type(obj) is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise CertError(f"{path}: non-string dict key")
            _assert_strict_json_types(v, f"{path}.{k}", depth + 1)
        return
    raise CertError(f"{path}: disallowed type {type(obj).__name__} (non-exact types forbidden)")


def _require_exact_keys(d: Any, expected: set[str], label: str) -> Dict[str, Any]:
    if type(d) is not dict:
        raise CertError(f"{label}: expected dict")
    keys = set(d.keys())
    if keys != expected:
        missing = sorted(expected - keys)
        extra = sorted(keys - expected)
        raise CertError(f"{label}: key mismatch (missing={missing}, extra={extra})")
    return d


def _parse_bool(v: Any, label: str) -> bool:
    if type(v) is not bool:
        raise CertError(f"{label}: expected bool, got {type(v).__name__}")
    return v


def _parse_int(v: Any, label: str, lo: Optional[int] = None, hi: Optional[int] = None) -> int:
    if type(v) is not int:
        raise CertError(f"{label}: expected int, got {type(v).__name__}")
    if v.bit_length() > MAX_BIT_LEN:
        raise CertError(f"{label}: integer exceeds {MAX_BIT_LEN} bits")
    if lo is not None and v < lo:
        raise CertError(f"{label}: {v} < {lo}")
    if hi is not None and v > hi:
        raise CertError(f"{label}: {v} > {hi}")
    return v


def _parse_id_str(v: Any, label: str) -> str:
    if type(v) is not str or not v or len(v) > MAX_ID_LEN:
        raise CertError(f"{label}: expected non-empty string of length <= {MAX_ID_LEN}")
    if any(ord(ch) < 32 or ord(ch) == 127 for ch in v):
        raise CertError(f"{label}: ASCII control characters disallowed")
    return v


def _parse_int_list(
    v: Any,
    label: str,
    min_len: int = 0,
    max_len: int = 64,
    lo: Optional[int] = None,
    hi: Optional[int] = None,
) -> List[int]:
    if type(v) is not list or not (min_len <= len(v) <= max_len):
        raise CertError(f"{label}: expected list of length {min_len}..{max_len}")
    return [_parse_int(x, f"{label}[{i}]", lo, hi) for i, x in enumerate(v)]


def _parse_game_tree(node: Any, label: str = "tree", depth: int = 0, leaf_budget: List[int] | None = None) -> Dict[str, Any]:
    if leaf_budget is None:
        leaf_budget = [256]
    if depth > 8:
        raise CertError(f"{label}: game tree depth exceeds 8")
    if type(node) is not dict or "kind" not in node:
        raise CertError(f"{label}: expected dict with 'kind'")
    kind = _parse_id_str(node["kind"], f"{label}.kind")
    if kind == "leaf":
        _require_exact_keys(node, {"kind", "val"}, label)
        val = _parse_int(node["val"], f"{label}.val", -1000000, 1000000)
        leaf_budget[0] -= 1
        if leaf_budget[0] < 0:
            raise CertError(f"{label}: leaf count exceeds 256")
        return {"kind": "leaf", "val": val}
    if kind in ("max", "min"):
        _require_exact_keys(node, {"kind", "moves", "children"}, label)
        moves = _parse_int_list(node["moves"], f"{label}.moves", 1, 12, -1000, 1000)
        if len(set(moves)) != len(moves):
            raise CertError(f"{label}.moves: duplicate move label")
        raw_ch = node["children"]
        if type(raw_ch) is not list or len(raw_ch) != len(moves):
            raise CertError(f"{label}.children: expected {len(moves)} child trees")
        children = [_parse_game_tree(ch, f"{label}.children[{i}]", depth + 1, leaf_budget) for i, ch in enumerate(raw_ch)]
        return {"kind": kind, "moves": moves, "children": children}
    raise CertError(f"{label}.kind: invalid kind {kind!r}")


def _verify_mode1(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Sec. 2, 3, 5 exact exhaustive vs. monadic continuation alpha-beta search trace."""
    _require_exact_keys(
        payload,
        {
            "tree",
            "alpha",
            "beta",
            "claimed_exhaustive_val",
            "claimed_exhaustive_play",
            "claimed_exhaustive_leaves",
            "claimed_ab_val",
            "claimed_ab_play",
            "claimed_ab_leaves",
            "claimed_ab_trace",
        },
        "mode1.payload",
    )
    tree = _parse_game_tree(payload["tree"], "tree")
    alpha = _parse_int(payload["alpha"], "alpha", -10000000, 10000000)
    beta = _parse_int(payload["beta"], "beta", -10000000, 10000000)
    if alpha >= beta:
        raise CertError("alpha must be strictly less than beta")

    (ex_val, ex_play), ex_leaves = eval_exhaustive(tree)
    (ab_val, ab_play), ab_trace = eval_monadic_ab(tree, alpha, beta)
    ab_leaves = len(ab_trace)

    # Check Theorem 1(i)-(iii) independently
    if ex_val <= alpha and not (ab_val <= alpha):
        raise CertError("Theorem 1(i) violated")
    if ex_val >= beta and not (ab_val >= beta):
        raise CertError("Theorem 1(ii) violated")
    if alpha < ex_val < beta and (ab_val, ab_play) != (ex_val, ex_play):
        raise CertError("Theorem 1(iii) violated")
    if ab_leaves > ex_leaves:
        raise CertError("Alpha-beta evaluated more leaves than exhaustive search")

    if _parse_int(payload["claimed_exhaustive_val"], "claimed_exhaustive_val") != ex_val:
        raise CertError("claimed_exhaustive_val mismatch")
    if _parse_int_list(payload["claimed_exhaustive_play"], "claimed_exhaustive_play", 0, 16) != ex_play:
        raise CertError("claimed_exhaustive_play mismatch")
    if _parse_int(payload["claimed_exhaustive_leaves"], "claimed_exhaustive_leaves", 1) != ex_leaves:
        raise CertError("claimed_exhaustive_leaves mismatch")
    if _parse_int(payload["claimed_ab_val"], "claimed_ab_val") != ab_val:
        raise CertError("claimed_ab_val mismatch")
    if _parse_int_list(payload["claimed_ab_play"], "claimed_ab_play", 0, 16) != ab_play:
        raise CertError("claimed_ab_play mismatch")
    if _parse_int(payload["claimed_ab_leaves"], "claimed_ab_leaves", 1) != ab_leaves:
        raise CertError("claimed_ab_leaves mismatch")

    raw_trace = payload["claimed_ab_trace"]
    if type(raw_trace) is not list or len(raw_trace) != ab_leaves:
        raise CertError(f"claimed_ab_trace: expected {ab_leaves} trace entries")
    for idx, entry in enumerate(raw_trace):
        if type(entry) is not list or len(entry) != 2:
            raise CertError(f"claimed_ab_trace[{idx}]: expected [path, val]")
        ep = _parse_int_list(entry[0], f"claimed_ab_trace[{idx}][0]", 0, 16)
        ev = _parse_int(entry[1], f"claimed_ab_trace[{idx}][1]")
        if (ep, ev) != ab_trace[idx]:
            raise CertError(f"claimed_ab_trace[{idx}] mismatch")

    return {
        "exhaustive_val": ex_val,
        "exhaustive_leaves": ex_leaves,
        "ab_val": ab_val,
        "ab_leaves": ab_leaves,
        "pruned_leaves": ex_leaves - ab_leaves,
    }


def _verify_mode2(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Sec. 4 Thm. 1(i)-(iii), Cor. 1(b), & Sec. 5 tie-breaking stability across windows."""
    _require_exact_keys(
        payload,
        {
            "tree",
            "claimed_exhaustive_val",
            "claimed_exhaustive_play",
            "window_checks",
        },
        "mode2.payload",
    )
    tree = _parse_game_tree(payload["tree"], "tree")
    (ex_val, ex_play), _ = eval_exhaustive(tree)
    if _parse_int(payload["claimed_exhaustive_val"], "claimed_exhaustive_val") != ex_val:
        raise CertError("claimed_exhaustive_val mismatch")
    if _parse_int_list(payload["claimed_exhaustive_play"], "claimed_exhaustive_play", 0, 16) != ex_play:
        raise CertError("claimed_exhaustive_play mismatch")

    raw_wins = payload["window_checks"]
    if type(raw_wins) is not list or not (1 <= len(raw_wins) <= 16):
        raise CertError("window_checks: expected 1..16 window records")

    regimes_seen: List[str] = []
    for i, w in enumerate(raw_wins):
        _require_exact_keys(
            w,
            {"alpha", "beta", "claimed_regime", "claimed_ab_val", "claimed_ab_play", "claimed_ab_leaves"},
            f"window_checks[{i}]",
        )
        a = _parse_int(w["alpha"], f"window_checks[{i}].alpha", -10000000, 10000000)
        b = _parse_int(w["beta"], f"window_checks[{i}].beta", -10000000, 10000000)
        if a >= b:
            raise CertError(f"window_checks[{i}]: alpha must be < beta")
        (ab_v, ab_p), tr = eval_monadic_ab(tree, a, b)

        if ex_val <= a:
            regime = "fail_low"
            if not (ab_v <= a):
                raise CertError(f"window_checks[{i}]: Theorem 1(i) violated")
        elif ex_val >= b:
            regime = "fail_high"
            if not (ab_v >= b):
                raise CertError(f"window_checks[{i}]: Theorem 1(ii) violated")
        else:
            regime = "exact_window"
            if (ab_v, ab_p) != (ex_val, ex_play):
                raise CertError(f"window_checks[{i}]: Theorem 1(iii) tie/play mismatch")

        # Also independently verify Corollary 1(b): if a < ab_v < b then (ab_v, ab_p) == (ex_val, ex_play)
        if a < ab_v < b and (ab_v, ab_p) != (ex_val, ex_play):
            raise CertError(f"window_checks[{i}]: Corollary 1(b) violated")

        if _parse_id_str(w["claimed_regime"], f"window_checks[{i}].claimed_regime") != regime:
            raise CertError(f"window_checks[{i}]: claimed_regime mismatch (expected {regime!r})")
        if _parse_int(w["claimed_ab_val"], f"window_checks[{i}].claimed_ab_val") != ab_v:
            raise CertError(f"window_checks[{i}]: claimed_ab_val mismatch")
        if _parse_int_list(w["claimed_ab_play"], f"window_checks[{i}].claimed_ab_play", 0, 16) != ab_p:
            raise CertError(f"window_checks[{i}]: claimed_ab_play mismatch")
        if _parse_int(w["claimed_ab_leaves"], f"window_checks[{i}].claimed_ab_leaves", 1) != len(tr):
            raise CertError(f"window_checks[{i}]: claimed_ab_leaves mismatch")
        regimes_seen.append(regime)

    return {
        "exhaustive_val": ex_val,
        "windows_checked": len(raw_wins),
        "regimes": regimes_seen,
    }


def _verify_mode3(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Sec. 5 Definition 2 & Corollary 2 ply-by-ply optimal play certification."""
    _require_exact_keys(
        payload,
        {
            "tree",
            "alpha",
            "beta",
            "claimed_optimal_val",
            "claimed_optimal_play",
            "claimed_ply_values",
            "claimed_def2_optimal",
        },
        "mode3.payload",
    )
    tree = _parse_game_tree(payload["tree"], "tree")
    alpha = _parse_int(payload["alpha"], "alpha", -10000000, 10000000)
    beta = _parse_int(payload["beta"], "beta", -10000000, 10000000)
    if alpha >= beta:
        raise CertError("alpha must be < beta")

    (ex_val, ex_play), _ = eval_exhaustive(tree)
    (ab_val, ab_play), _ = eval_monadic_ab(tree, alpha, beta)
    if not (alpha < ex_val < beta):
        raise CertError("Corollary 2 certificate requires alpha < out(G) < beta")
    if (ab_val, ab_play) != (ex_val, ex_play):
        raise CertError("Corollary 2 mismatch between monadic alpha-beta and exhaustive optimal play")

    def2_ok, ply_vals = verify_optimal_play_def2(tree, ab_play)
    if not def2_ok:
        raise CertError("Definition 2 optimal play verification failed along returned path")

    if _parse_int(payload["claimed_optimal_val"], "claimed_optimal_val") != ab_val:
        raise CertError("claimed_optimal_val mismatch")
    if _parse_int_list(payload["claimed_optimal_play"], "claimed_optimal_play", 0, 16) != ab_play:
        raise CertError("claimed_optimal_play mismatch")
    if _parse_int_list(payload["claimed_ply_values"], "claimed_ply_values", 1, 17) != ply_vals:
        raise CertError("claimed_ply_values mismatch")
    if _parse_bool(payload["claimed_def2_optimal"], "claimed_def2_optimal") is not True:
        raise CertError("claimed_def2_optimal must be True")

    return {
        "optimal_val": ab_val,
        "play_len": len(ab_play),
        "def2_verified": True,
    }


def _verify_mode4(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Sec. 6.2 history-dependent Tic-Tac-Toe monadic alpha-beta pruning & Cor. 1(b)."""
    _require_exact_keys(
        payload,
        {
            "prefix_moves",
            "alpha",
            "beta",
            "verify_exhaustive_subgame",
            "claimed_exhaustive_leaves",
            "claimed_ab_val",
            "claimed_ab_play",
            "claimed_ab_leaves",
            "claimed_cor1b_exact",
        },
        "mode4.payload",
    )
    prefix = _parse_int_list(payload["prefix_moves"], "prefix_moves", 0, 8, 0, 8)
    if len(set(prefix)) != len(prefix):
        raise CertError("prefix_moves: duplicate square index")
    alpha = _parse_int(payload["alpha"], "alpha", -10, 10)
    beta = _parse_int(payload["beta"], "beta", -10, 10)
    if alpha >= beta:
        raise CertError("alpha must be < beta")

    verify_ex = _parse_bool(payload["verify_exhaustive_subgame"], "verify_exhaustive_subgame")
    if verify_ex and len(prefix) < 3:
        raise CertError("verify_exhaustive_subgame=True only permitted for prefix length >= 3 (<= 720 leaves)")

    ex_leaves = _int_fact(9 - len(prefix))
    (ab_val, ab_play), ab_leaves = ttt_monadic_ab(prefix, alpha, beta)
    if len(ab_play) != 9 or sorted(ab_play) != list(range(9)) or ab_play[: len(prefix)] != prefix:
        raise CertError("Returned Tic-Tac-Toe play is not a valid full permutation extending prefix")

    if verify_ex:
        (ex_val, ex_play), ex_cnt = ttt_exhaustive(prefix)
        if ex_cnt != ex_leaves:
            raise CertError("Internal factorial leaf count mismatch")
        if alpha < ab_val < beta and (ab_val, ab_play) != (ex_val, ex_play):
            raise CertError("Corollary 1(b) violated on Tic-Tac-Toe subgame")

    cor1b_exact = alpha < ab_val < beta
    if _parse_int(payload["claimed_exhaustive_leaves"], "claimed_exhaustive_leaves", 1) != ex_leaves:
        raise CertError(f"claimed_exhaustive_leaves mismatch: expected {ex_leaves}")
    if _parse_int(payload["claimed_ab_val"], "claimed_ab_val", -1, 1) != ab_val:
        raise CertError(f"claimed_ab_val mismatch: expected {ab_val}")
    if _parse_int_list(payload["claimed_ab_play"], "claimed_ab_play", 9, 9, 0, 8) != ab_play:
        raise CertError("claimed_ab_play mismatch")
    if _parse_int(payload["claimed_ab_leaves"], "claimed_ab_leaves", 1, ex_leaves) != ab_leaves:
        raise CertError(f"claimed_ab_leaves mismatch: expected {ab_leaves}")
    if _parse_bool(payload["claimed_cor1b_exact"], "claimed_cor1b_exact") != cor1b_exact:
        raise CertError("claimed_cor1b_exact mismatch")

    return {
        "prefix_len": len(prefix),
        "exhaustive_leaves": ex_leaves,
        "ab_val": ab_val,
        "ab_leaves": ab_leaves,
        "cor1b_exact": cor1b_exact,
    }


def verify_certificate(cert: Any) -> Tuple[bool, str, Dict[str, Any]]:
    """Verify an ALPHABETA-MONAD-CERT-1.0 certificate payload with zero floating-point arithmetic."""
    try:
        _assert_strict_json_types(cert)
        _require_exact_keys(
            cert,
            {"schema_version", "cert_id", "mode", "reference", "payload"},
            "certificate",
        )
        if cert["schema_version"] != SCHEMA_VERSION:
            raise CertError(
                f"schema_version mismatch: expected {SCHEMA_VERSION!r}, got {cert['schema_version']!r}"
            )
        cert_id = _parse_id_str(cert["cert_id"], "cert_id")
        mode = _parse_id_str(cert["mode"], "mode")
        if mode not in VALID_MODES:
            raise CertError(f"unknown mode {mode!r}")
        _parse_id_str(cert["reference"], "reference")
        payload = cert["payload"]
        if type(payload) is not dict:
            raise CertError("payload must be a dict")

        if mode == "fixed_tree_alphabeta_cert":
            summary = _verify_mode1(payload)
        elif mode == "tie_breaking_and_window_cert":
            summary = _verify_mode2(payload)
        elif mode == "optimal_play_witness_cert":
            summary = _verify_mode3(payload)
        else:
            summary = _verify_mode4(payload)

        summary["cert_id"] = cert_id
        summary["mode"] = mode
        return True, "OK", summary
    except CertError as exc:
        return False, str(exc), {}
