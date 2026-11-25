# Certified Verification of Alpha-Beta Pruning via Monadic Continuations

[![License: MIT](https://img.shields.io/badge/Code%20%26%20Lean-MIT-blue.svg)](LICENSE)
[![Paper License: CC-BY-4.0](https://img.shields.io/badge/Paper-CC--BY--4.0-green.svg)](paper/main.tex)

**Author:** Lluis Eriksson

Machine-checked **Lean 4.35.0** formalization and zero-floating-point exact discrete certificate audit (`ALPHABETA-MONAD-CERT-1.0`) for **Martín Hötzel Escardó and Paulo Oliva** ([arXiv:2611.32320](https://arxiv.org/abs/2611.32320), Nov 24, 2026), *"Alpha-Beta Pruning via Monadic Continuations"*.

---

## Key Verified Artifacts

| Artifact | Verification Metric | Result |
| :--- | :--- | :--- |
| **Lean 4.35.0 Kernel** (`lean/AlphaBetaMonadic.lean`) | 18 theorems, zero `sorry`, zero warnings, zero `Classical.choice` | **18 / 18 PASS** (`8` `none`, `10` `[propext, Quot.sound]`) |
| **Exact Discrete Verifier** (`src/alphabeta_certifier.py`) | Zero `float()`, `math.`, or `numpy`; 4-mode `ALPHABETA-MONAD-CERT-1.0` | **16 / 16 PASS** (`0.092–103.002 ms`, total `124.66 ms`) |
| **Adversarial Red-Team Suite** (`tests/test_suite.py`) | 60 live forged payloads (12 global + 12/mode) | **60 / 60 REJECTED** |
| **SHA-256 Integrity Manifest** (`SHA256_MANIFEST.json`) | Full deterministic replay check (`scripts/verify_all.py`) | **39 / 39 MATCH** |
| **Manuscript** (`paper/main.pdf`) | 3 pages, 3 publication figures (`300 DPI`) | **0 warnings, 0 overfulls** |

---

## Four Certificate Modes (`ALPHABETA-MONAD-CERT-1.0`)

1. **`fixed_tree_alphabeta_cert` (Mode 1 — Sec. 2.2/3.3/5):** Replays exhaustive minimax and monadic continuation alpha-beta on arbitrary finite game trees, verifying exact values, optimal plays, leaf counts, Theorem 1(i)--(iii) soundness, and exact ordered leaf-evaluation traces (including the 36-leaf -> 18-leaf Wikipedia tree).
2. **`tie_breaking_and_window_cert` (Mode 2 — Thm. 1 & Cor. 1(b)):** Stress-tests multiple aspiration and boundary windows $(\alpha, \beta)$ on one tree, classifying `exact_window`, `fail_low`, and `fail_high` regimes, verifying Corollary 1(b), and auditing first-element tie-breaking against Section 5 pruned-bound traps.
3. **`optimal_play_witness_cert` (Mode 3 — Def. 2 & Cor. 2):** Independently checks ply-by-ply optimality of the extracted play against exact subgame minimax values at every internal node.
4. **`history_dependent_ttt_cert` (Mode 4 — Sec. 6.2):** Replays exact history-dependent monadic alpha-beta on $3\times 3$ Tic-Tac-Toe, including Escardó & Oliva's exact root benchmark (`9! = 362,880 -> 9,335` evaluated plays, `38.873x` speedup, value `0`, optimal draw play `[0,4,1,2,6,3,5,7,8]`).

---

## Quick Reproduction

```bash
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```

---

## Licenses & Transparency Disclosure

- **Code, Lean proofs, certificates, and scripts:** [MIT License](LICENSE).
- **Manuscript (`paper/main.tex`, `paper/main.pdf`) and figures:** CC-BY-4.0.
- **AI Assistance Disclosure:** Prepared by sole author Lluis Eriksson with AI coding, formalization, and drafting assistance from Google Antigravity; all Lean proofs, exact discrete certificates, and adversarial tests were independently compiled and machine-verified locally.
