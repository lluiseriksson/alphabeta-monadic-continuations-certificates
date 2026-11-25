"""Live 60-attack adversarial red-team test suite for ALPHABETA-MONAD-CERT-1.0.

Tests 12 global schema/typing/depth/control-char attacks + 12 domain attacks per mode.
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
from typing import Any, Callable, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.alphabeta_certifier import verify_certificate


def _load(name: str) -> dict[str, Any]:
    return json.loads((ROOT / "certificates" / f"{name}.json").read_text(encoding="utf-8"))


def _mutate(cert: dict[str, Any], fn: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    c = copy.deepcopy(cert)
    fn(c)
    return c


def build_attacks() -> List[Tuple[str, str, Any]]:
    m1 = _load("m1_wiki_36leaf_to_18leaf")
    m2 = _load("m2_tie_trap_boundary_windows")
    m3 = _load("m3_opt_play_wiki_1000")
    m4 = _load("m4_ttt_subgame_ply4_forced_draw")

    attacks: List[Tuple[str, str, Any]] = []

    # --- 12 Global Schema / Type / Depth / Control-Char Attacks ---
    attacks.append(("global", "g01_wrong_schema_version", _mutate(m1, lambda c: c.__setitem__("schema_version", "ALPHABETA-MONAD-CERT-2.0"))))
    attacks.append(("global", "g02_unknown_mode", _mutate(m1, lambda c: c.__setitem__("mode", "bogus_mode"))))
    attacks.append(("global", "g03_extra_top_key", _mutate(m1, lambda c: c.__setitem__("extra", 1))))
    attacks.append(("global", "g04_missing_payload_key", _mutate(m1, lambda c: c["payload"].pop("alpha"))))
    attacks.append(("global", "g05_raw_float_injected", _mutate(m1, lambda c: c["payload"].__setitem__("alpha", -1000.0))))
    attacks.append(("global", "g06_bool_as_int_alpha", _mutate(m1, lambda c: c["payload"].__setitem__("alpha", True))))
    attacks.append(("global", "g07_int_as_bool_def2", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_def2_optimal", 1))))
    attacks.append(("global", "g08_nul_control_char_in_id", _mutate(m1, lambda c: c.__setitem__("cert_id", "bad\x00id"))))
    attacks.append(("global", "g09_esc_control_char_in_ref", _mutate(m1, lambda c: c.__setitem__("reference", "bad\x1bref"))))
    attacks.append(("global", "g10_excess_id_len", _mutate(m1, lambda c: c.__setitem__("cert_id", "a" * 200))))
    attacks.append(("global", "g11_excess_int_bits", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_ab_val", 1 << 2100))))

    def _deep_nest(c: dict[str, Any]) -> None:
        node: Any = "leaf"
        for _ in range(40):
            node = [node]
        c["payload"]["claimed_ab_trace"] = node

    attacks.append(("global", "g12_excess_json_depth", _mutate(m1, _deep_nest)))

    # --- 12 Mode 1 Domain Attacks ---
    attacks.append(("mode1", "m1_01_alpha_ge_beta", _mutate(m1, lambda c: c["payload"].__setitem__("alpha", 1000))))
    attacks.append(("mode1", "m1_02_invalid_tree_kind", _mutate(m1, lambda c: c["payload"]["tree"].__setitem__("kind", "chance"))))
    attacks.append(("mode1", "m1_03_duplicate_move_label", _mutate(m1, lambda c: c["payload"]["tree"].__setitem__("moves", [0, 0, 2]))))
    attacks.append(("mode1", "m1_04_moves_children_mismatch", _mutate(m1, lambda c: c["payload"]["tree"]["children"].pop())))
    attacks.append(("mode1", "m1_05_wrong_exhaustive_val", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_exhaustive_val", 5))))
    attacks.append(("mode1", "m1_06_wrong_exhaustive_play", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_exhaustive_play", [0, 0, 0, 0]))))
    attacks.append(("mode1", "m1_07_wrong_exhaustive_leaves", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_exhaustive_leaves", 35))))
    attacks.append(("mode1", "m1_08_wrong_ab_val", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_ab_val", 7))))
    attacks.append(("mode1", "m1_09_wrong_ab_play", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_ab_play", [1, 0, 1, 0]))))
    attacks.append(("mode1", "m1_10_wrong_ab_leaves", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_ab_leaves", 17))))
    attacks.append(("mode1", "m1_11_tampered_trace_entry", _mutate(m1, lambda c: c["payload"]["claimed_ab_trace"][0].__setitem__(1, 99))))
    attacks.append(("mode1", "m1_12_nonlist_trace_no_crash", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_ab_trace", "bad"))))

    # --- 12 Mode 2 Domain Attacks ---
    attacks.append(("mode2", "m2_01_empty_window_checks", _mutate(m2, lambda c: c["payload"].__setitem__("window_checks", []))))
    attacks.append(("mode2", "m2_02_wrong_ex_val", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_exhaustive_val", 4))))
    attacks.append(("mode2", "m2_03_wrong_ex_play_tie_swap", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_exhaustive_play", [1, 0]))))
    attacks.append(("mode2", "m2_04_window_alpha_ge_beta", _mutate(m2, lambda c: c["payload"]["window_checks"][0].__setitem__("alpha", 10))))
    attacks.append(("mode2", "m2_05_wrong_regime_label", _mutate(m2, lambda c: c["payload"]["window_checks"][0].__setitem__("claimed_regime", "fail_low"))))
    attacks.append(("mode2", "m2_06_wrong_ab_val_window", _mutate(m2, lambda c: c["payload"]["window_checks"][0].__setitem__("claimed_ab_val", 6))))
    attacks.append(("mode2", "m2_07_displaced_tie_play", _mutate(m2, lambda c: c["payload"]["window_checks"][1].__setitem__("claimed_ab_play", [1, 0]))))
    attacks.append(("mode2", "m2_08_wrong_ab_leaves_window", _mutate(m2, lambda c: c["payload"]["window_checks"][0].__setitem__("claimed_ab_leaves", 1))))
    attacks.append(("mode2", "m2_09_extra_window_key", _mutate(m2, lambda c: c["payload"]["window_checks"][0].__setitem__("extra", 0))))
    attacks.append(("mode2", "m2_10_missing_window_key", _mutate(m2, lambda c: c["payload"]["window_checks"][0].pop("beta"))))
    attacks.append(("mode2", "m2_11_nonlist_windows_no_crash", _mutate(m2, lambda c: c["payload"].__setitem__("window_checks", 123))))
    attacks.append(("mode2", "m2_12_nondict_tree_no_crash", _mutate(m2, lambda c: c["payload"].__setitem__("tree", []))))

    # --- 12 Mode 3 Domain Attacks ---
    attacks.append(("mode3", "m3_01_alpha_ge_beta", _mutate(m3, lambda c: c["payload"].__setitem__("alpha", 1000))))
    attacks.append(("mode3", "m3_02_out_not_in_window_low", _mutate(m3, lambda c: c["payload"].__setitem__("alpha", 6))))
    attacks.append(("mode3", "m3_03_out_not_in_window_high", _mutate(m3, lambda c: c["payload"].__setitem__("beta", 6))))
    attacks.append(("mode3", "m3_04_wrong_opt_val", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_optimal_val", 5))))
    attacks.append(("mode3", "m3_05_suboptimal_play_claimed", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_optimal_play", [0, 0, 0, 0]))))
    attacks.append(("mode3", "m3_06_truncated_play", _mutate(m3, lambda c: c["payload"]["claimed_optimal_play"].pop())))
    attacks.append(("mode3", "m3_07_wrong_ply_values", _mutate(m3, lambda c: c["payload"]["claimed_ply_values"].__setitem__(2, 5))))
    attacks.append(("mode3", "m3_08_truncated_ply_values", _mutate(m3, lambda c: c["payload"]["claimed_ply_values"].pop())))
    attacks.append(("mode3", "m3_09_false_def2_optimal", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_def2_optimal", False))))
    attacks.append(("mode3", "m3_10_invalid_leaf_val_type", _mutate(m3, lambda c: c["payload"]["tree"].__setitem__("moves", ["a", "b", "c"]))))
    attacks.append(("mode3", "m3_11_empty_moves_list", _mutate(m3, lambda c: c["payload"]["tree"].__setitem__("moves", []))))
    attacks.append(("mode3", "m3_12_nonlist_play_no_crash", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_optimal_play", "1000"))))

    # --- 12 Mode 4 Domain Attacks ---
    attacks.append(("mode4", "m4_01_duplicate_prefix_square", _mutate(m4, lambda c: c["payload"].__setitem__("prefix_moves", [0, 4, 1, 0]))))
    attacks.append(("mode4", "m4_02_square_out_of_range", _mutate(m4, lambda c: c["payload"].__setitem__("prefix_moves", [0, 4, 1, 9]))))
    attacks.append(("mode4", "m4_03_alpha_ge_beta", _mutate(m4, lambda c: c["payload"].__setitem__("alpha", 1))))
    attacks.append(("mode4", "m4_04_verify_ex_on_root_disallowed", _mutate(m4, lambda c: c["payload"].__setitem__("prefix_moves", []))))
    attacks.append(("mode4", "m4_05_wrong_ex_leaves", _mutate(m4, lambda c: c["payload"].__setitem__("claimed_exhaustive_leaves", 121))))
    attacks.append(("mode4", "m4_06_wrong_ab_val", _mutate(m4, lambda c: c["payload"].__setitem__("claimed_ab_val", 1))))
    attacks.append(("mode4", "m4_07_wrong_ab_play", _mutate(m4, lambda c: c["payload"]["claimed_ab_play"].reverse())))
    attacks.append(("mode4", "m4_08_wrong_ab_leaves", _mutate(m4, lambda c: c["payload"].__setitem__("claimed_ab_leaves", 1))))
    attacks.append(("mode4", "m4_09_wrong_cor1b_exact", _mutate(m4, lambda c: c["payload"].__setitem__("claimed_cor1b_exact", False))))
    attacks.append(("mode4", "m4_10_int_as_bool_verify_ex", _mutate(m4, lambda c: c["payload"].__setitem__("verify_exhaustive_subgame", 1))))
    attacks.append(("mode4", "m4_11_int_as_bool_cor1b", _mutate(m4, lambda c: c["payload"].__setitem__("claimed_cor1b_exact", 1))))
    attacks.append(("mode4", "m4_12_nonlist_prefix_no_crash", _mutate(m4, lambda c: c["payload"].__setitem__("prefix_moves", 42))))

    assert len(attacks) == 60, f"Expected 60 attacks, got {len(attacks)}"
    return attacks


def run_red_team_suite() -> Tuple[int, int, List[str]]:
    attacks = build_attacks()
    rejected = 0
    failures: List[str] = []
    for cat, name, payload in attacks:
        ok, _, _ = verify_certificate(payload)
        if not ok:
            rejected += 1
        else:
            failures.append(f"[{cat}] {name} was UNEXPECTEDLY ACCEPTED!")
    return rejected, len(attacks), failures


def main() -> None:
    rejected, total, failures = run_red_team_suite()
    if failures:
        for f in failures:
            print("FAIL:", f)
        sys.exit(1)
    print(f"Adversarial red-team audit: {rejected}/{total} forged payloads REJECTED (100%).")


if __name__ == "__main__":
    main()
