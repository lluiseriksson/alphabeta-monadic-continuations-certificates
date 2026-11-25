"""Exact discrete game-tree minimax, monadic continuation + reader alpha-beta, and Tic-Tac-Toe helpers.

Strictly zero floating-point operations (uses int, bool, str, list, tuple exclusively).
Reproduces Escardo & Oliva (arXiv:2611.32320, Nov 24, 2026) Sec. 2-6 verbatim.
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from typing import Any, Dict, List, Sequence, Tuple

Outcome = Tuple[int, List[int]]


def pick_max(outcomes: Sequence[Outcome]) -> Outcome:
    """First-element-preserving max (pickMax of Sec. 5 / App. A)."""
    best = outcomes[0]
    for o in outcomes[1:]:
        if o[0] > best[0]:
            best = o
    return best


def pick_min(outcomes: Sequence[Outcome]) -> Outcome:
    """First-element-preserving min (pickMin of Sec. 5 / App. A)."""
    best = outcomes[0]
    for o in outcomes[1:]:
        if o[0] < best[0]:
            best = o
    return best


def eval_exhaustive(node: Dict[str, Any], path: List[int] | None = None) -> Tuple[Outcome, int]:
    """Exhaustive continuation-monad minimax returning ((val, play), leaf_count)."""
    if path is None:
        path = []
    if node["kind"] == "leaf":
        return (int(node["val"]), list(path)), 1
    outs: List[Outcome] = []
    leaves = 0
    for move, child in zip(node["moves"], node["children"]):
        o, c = eval_exhaustive(child, path + [int(move)])
        outs.append(o)
        leaves += c
    if node["kind"] == "max":
        return pick_max(outs), leaves
    return pick_min(outs), leaves


def eval_monadic_ab(
    node: Dict[str, Any],
    alpha: int,
    beta: int,
    path: List[int] | None = None,
    trace: List[Tuple[List[int], int]] | None = None,
) -> Tuple[Outcome, List[Tuple[List[int], int]]]:
    """Exact monadic continuation + reader alpha-beta search (Sec. 3.1 & Sec. 5)."""
    if path is None:
        path = []
    if trace is None:
        trace = []
    if node["kind"] == "leaf":
        val = int(node["val"])
        trace.append((list(path), val))
        return (val, list(path)), trace

    if node["kind"] == "max":
        cur_a = alpha
        collected: List[Outcome] = []
        for move, child in zip(node["moves"], node["children"]):
            o, _ = eval_monadic_ab(child, cur_a, beta, path + [int(move)], trace)
            collected.append(o)
            if o[0] >= beta:
                break
            if o[0] > cur_a:
                cur_a = o[0]
        return pick_max(collected), trace

    cur_b = beta
    collected = []
    for move, child in zip(node["moves"], node["children"]):
        o, _ = eval_monadic_ab(child, alpha, cur_b, path + [int(move)], trace)
        collected.append(o)
        if o[0] <= alpha:
            break
        if o[0] < cur_b:
            cur_b = o[0]
    return pick_min(collected), trace


def verify_optimal_play_def2(node: Dict[str, Any], play: Sequence[int]) -> Tuple[bool, List[int]]:
    """Verify Escardo & Oliva Definition 2: out(G_{s_k . x_k}) = out(G_{s_k}) at every ply k."""
    cur = node
    root_out, _ = eval_exhaustive(cur, [])
    ply_vals = [root_out[0]]
    prefix: List[int] = []
    for m in play:
        if cur["kind"] == "leaf":
            return False, ply_vals
        moves = cur["moves"]
        if m not in moves:
            return False, ply_vals
        idx = moves.index(m)
        child = cur["children"][idx]
        child_out, _ = eval_exhaustive(child, prefix + [m])
        if child_out[0] != ply_vals[-1]:
            return False, ply_vals
        ply_vals.append(child_out[0])
        prefix.append(m)
        cur = child
    if cur["kind"] != "leaf":
        return False, ply_vals
    return True, ply_vals


# --- Exact Tic-Tac-Toe (Escardo & Oliva Section 6.2 verbatim!) ---

TTT_WIN_LINES: Tuple[Tuple[int, int, int], ...] = (
    (0, 1, 2),
    (3, 4, 5),
    (6, 7, 8),
    (0, 3, 6),
    (1, 4, 7),
    (2, 5, 8),
    (0, 4, 8),
    (2, 4, 6),
)


def ttt_wins(squares: Sequence[int]) -> bool:
    s = set(squares)
    return any(a in s and b in s and c in s for a, b, c in TTT_WIN_LINES)


def ttt_leaf_value(play: Sequence[int]) -> int:
    """Exact outcome function q' from Escardo & Oliva Sec. 6.2 (stops recording after a win)."""
    xs: List[int] = []
    os: List[int] = []
    for ply, sq in enumerate(play):
        if ply % 2 == 0:
            if ttt_wins(os):
                break
            xs.append(sq)
        else:
            if ttt_wins(xs):
                break
            os.append(sq)
    if ttt_wins(xs):
        return 1
    if ttt_wins(os):
        return -1
    return 0


def ttt_monadic_ab(prefix: Sequence[int], alpha: int, beta: int) -> Tuple[Outcome, int]:
    """Exact history-dependent monadic alpha-beta search on Tic-Tac-Toe (Sec. 6.2 verbatim)."""
    used = set(prefix)
    avail = [sq for sq in range(9) if sq not in used]
    if not avail:
        return (ttt_leaf_value(prefix), list(prefix)), 1
    is_max = (len(prefix) % 2) == 0
    total_evals = 0
    if is_max:
        cur_a = alpha
        best: Outcome | None = None
        for sq in avail:
            o, cnt = ttt_monadic_ab(list(prefix) + [sq], cur_a, beta)
            total_evals += cnt
            if best is None or o[0] > best[0]:
                best = o
            if o[0] >= beta:
                break
            if o[0] > cur_a:
                cur_a = o[0]
        assert best is not None
        return best, total_evals
    cur_b = beta
    best = None
    for sq in avail:
        o, cnt = ttt_monadic_ab(list(prefix) + [sq], alpha, cur_b)
        total_evals += cnt
        if best is None or o[0] < best[0]:
            best = o
        if o[0] <= alpha:
            break
        if o[0] < cur_b:
            cur_b = o[0]
    assert best is not None
    return best, total_evals


def ttt_exhaustive(prefix: Sequence[int]) -> Tuple[Outcome, int]:
    """Exact exhaustive minimax on Tic-Tac-Toe subgame from prefix."""
    used = set(prefix)
    avail = [sq for sq in range(9) if sq not in used]
    if not avail:
        return (ttt_leaf_value(prefix), list(prefix)), 1
    is_max = (len(prefix) % 2) == 0
    total_evals = 0
    outs: List[Outcome] = []
    for sq in avail:
        o, cnt = ttt_exhaustive(list(prefix) + [sq])
        total_evals += cnt
        outs.append(o)
    return (pick_max(outs) if is_max else pick_min(outs)), total_evals
