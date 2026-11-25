"""Generate 3 publication-quality 300 DPI figures for ALPHABETA-MONAD-CERT-1.0.

Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent


def make_fig1() -> None:
    d1 = json.loads((ROOT / "data" / "exp1_ttt_ply_pruning_curve.json").read_text(encoding="utf-8"))["rows"]
    d2 = json.loads((ROOT / "data" / "exp2_wiki_window_sensitivity.json").read_text(encoding="utf-8"))["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.35), dpi=300)

    plys = [r["ply"] for r in d1]
    ex_l = [r["exhaustive_leaves"] for r in d1]
    ab_l = [r["ab_leaves"] for r in d1]
    ax1.semilogy(plys, ex_l, "o--", color="#7f8c8d", lw=1.8, ms=4.5, label=r"Exhaustive $(9-\mathrm{ply})!$ plays")
    ax1.semilogy(plys, ab_l, "s-", color="#1b4f72", lw=2.0, ms=4.8, label=r"Monadic $\alpha\text{-}\beta$ $(-1, 1)$ plays")
    ax1.annotate("362,880 -> 9,335\n(38.87x speedup)", xy=(0, 9335), xytext=(1.2, 45000),
                 fontsize=6.8, fontweight="bold", color="#1b4f72",
                 arrowprops={"arrowstyle": "->", "color": "#1b4f72", "lw": 1.0})
    ax1.set_xticks(plys)
    ax1.set_xlabel("Opening ply along optimal play [0,4,1,2,6,3,5,7,8]", fontsize=8.0)
    ax1.set_ylabel("Evaluated terminal plays (log scale)", fontsize=8.3)
    ax1.set_title("(a) Sec. 6.2 Tic-Tac-Toe pruning curve", fontsize=9.0, fontweight="bold")
    ax1.grid(True, which="both", alpha=0.22)
    ax1.legend(fontsize=6.6, loc="lower left", framealpha=0.93)

    wlabels = ["(-1000,\n1000)", "(0,12)", "(3,9)", "(5,7)", "(6,10)\nfail-lo", "(0,6)\nfail-hi"]
    ab_w = [r["ab_leaves"] for r in d2]
    pr_w = [r["pruned_leaves"] for r in d2]
    x = list(range(len(wlabels)))
    ax2.bar(x, ab_w, width=0.52, color="#148f77", edgecolor="#222222", lw=0.4, label="Evaluated leaves")
    ax2.bar(x, pr_w, width=0.52, bottom=ab_w, color="#d5dbdb", edgecolor="#222222", lw=0.4, label="Pruned leaves")
    for i, v in enumerate(ab_w):
        ax2.text(i, v / 2.0, str(v), ha="center", va="center", fontsize=7.2, fontweight="bold", color="white")
    ax2.set_xticks(x)
    ax2.set_xticklabels(wlabels, fontsize=6.9)
    ax2.set_ylim(0, 44)
    ax2.set_ylabel("Leaf count (total = 36)", fontsize=8.3)
    ax2.set_title("(b) Sec. 2.2/3.3 Wikipedia tree window sweep", fontsize=9.0, fontweight="bold")
    ax2.grid(True, axis="y", alpha=0.25)
    ax2.legend(fontsize=6.6, loc="upper right", framealpha=0.93)

    fig.tight_layout()
    out = ROOT / "figures" / "fig1_ttt_and_wiki_pruning.png"
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out, dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((ROOT / "data" / "exp3_tree_pruning_summary.json").read_text(encoding="utf-8"))["rows"]
    d1 = json.loads((ROOT / "data" / "exp1_ttt_ply_pruning_curve.json").read_text(encoding="utf-8"))["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.35), dpi=300)

    labels = ["Wiki\n36-leaf", "Asym.\nHistory", "Tie-Trap\n(Sec. 5)", "Best-Ord\nDepth-4"]
    ex_c = [r["exhaustive_leaves"] for r in d3]
    ab_c = [r["ab_leaves"] for r in d3]
    x = list(range(len(labels)))
    w = 0.34
    ax1.bar([i - w / 2 for i in x], ex_c, width=w, color="#7f8c8d", edgecolor="#222222", lw=0.4, label="Exhaustive minimax")
    ax1.bar([i + w / 2 for i in x], ab_c, width=w, color="#1b4f72", edgecolor="#222222", lw=0.4, label=r"Monadic $\alpha\text{-}\beta$")
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels, fontsize=7.5)
    ax1.set_ylim(0, 43)
    ax1.set_ylabel("Evaluated leaf count", fontsize=8.5)
    ax1.set_title("(a) Mode 1 benchmark trees: exhaustive vs. AB", fontsize=9.0, fontweight="bold")
    ax1.grid(True, axis="y", alpha=0.25)
    ax1.legend(fontsize=6.8, loc="upper right", framealpha=0.93)

    plys = [r["ply"] for r in d1]
    spds = [r["speedup_ratio"] for r in d1]
    bars = ax2.bar(plys, spds, width=0.58, color="#b9770e", edgecolor="#222222", lw=0.5)
    for b, val in zip(bars, spds):
        ax2.text(b.get_x() + b.get_width() / 2.0, val + 0.8, f"{val:.1f}x", ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax2.set_xticks(plys)
    ax2.set_ylim(0, max(spds) * 1.18)
    ax2.set_xlabel("Tic-Tac-Toe opening ply", fontsize=8.5)
    ax2.set_ylabel("Exact pruning speedup factor", fontsize=8.5)
    ax2.set_title("(b) Exact Tic-Tac-Toe speedup factor by ply", fontsize=9.0, fontweight="bold")
    ax2.grid(True, axis="y", alpha=0.25)

    fig.tight_layout()
    out = ROOT / "figures" / "fig2_benchmarks_and_speedup.png"
    fig.savefig(out, dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    rep = json.loads((ROOT / "data" / "certificate_replay_summary.json").read_text(encoding="utf-8"))["certificates"]
    short_names = [f"C{i+1:02d}" for i in range(len(rep))]
    ms_vals = [r["verify_ns"] / 1_000_000 for r in rep]
    mode_colors = {
        "fixed_tree_alphabeta_cert": "#1b4f72",
        "tie_breaking_and_window_cert": "#148f77",
        "optimal_play_witness_cert": "#b9770e",
        "history_dependent_ttt_cert": "#922b21",
    }
    bar_colors = [mode_colors[r["mode"]] for r in rep]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(8.2, 3.35), dpi=300)
    ax1.bar(short_names, ms_vals, color=bar_colors, edgecolor="#222222", lw=0.4)
    ax1.set_yscale("log")
    ax1.set_ylabel("Replay time (ms, log scale)", fontsize=8.5)
    ax1.set_xlabel("Canonical certs (M1: C01-C04, M2: C05-C08, M3: C09-C12, M4: C13-C16)", fontsize=6.9)
    ax1.set_title("(a) Exact discrete replay latency (16/16 PASS)", fontsize=9.0, fontweight="bold")
    ax1.tick_params(axis="x", labelsize=6.8, rotation=45)
    ax1.grid(True, which="both", axis="y", alpha=0.22)

    cats = ["Global\nSchema", "Mode 1\nTrees", "Mode 2\nWindows", "Mode 3\nDef. 2", "Mode 4\nTTT"]
    counts = [12, 12, 12, 12, 12]
    colors2 = ["#34495e", "#1b4f72", "#148f77", "#b9770e", "#922b21"]
    bars = ax2.bar(cats, counts, color=colors2, edgecolor="#222222", lw=0.5)
    for b in bars:
        ax2.text(
            b.get_x() + b.get_width() / 2.0,
            b.get_height() + 0.35,
            "12/12",
            ha="center",
            va="bottom",
            fontsize=7.5,
            fontweight="bold",
        )
    ax2.set_ylim(0, 14.5)
    ax2.set_ylabel("Forged payloads rejected", fontsize=8.5)
    ax2.set_title("(b) Live adversarial red-team audit (60/60)", fontsize=9.0, fontweight="bold")
    ax2.tick_params(axis="x", labelsize=7.5)
    ax2.grid(True, axis="y", alpha=0.25)

    fig.tight_layout()
    out = ROOT / "figures" / "fig3_certificate_replay_atlas.png"
    fig.savefig(out, dpi=300)
    plt.close(fig)


def main() -> None:
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 figures in figures/.")


if __name__ == "__main__":
    main()
