"""Exact rational lazy random-walk, spectral/trace, trimming, cut-farness, and non-backtracking helpers over Q.

Strictly zero floating-point operations (uses int and fractions.Fraction exclusively).
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Set, Tuple


def frac_to_canon_str(x: Fraction) -> str:
    if not isinstance(x, Fraction):
        raise TypeError("Expected Fraction")
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def int_gcd(a: int, b: int) -> int:
    x, y = abs(a), abs(b)
    while y:
        x, y = y, x % y
    return x


def build_lazy_walk_matrix(n: int, d: int, edges: Sequence[Tuple[int, int]]) -> List[List[Fraction]]:
    """Construct P = I - L_G / (2d) over exact Q (Melissaris Sec. 3.1)."""
    P = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    deg = [0] * n
    step_p = Fraction(1, 2 * d)
    for u, v in edges:
        P[u][v] = step_p
        P[v][u] = step_p
        deg[u] += 1
        deg[v] += 1
    for u in range(n):
        P[u][u] = Fraction(2 * d - deg[u], 2 * d)
    return P


def mat_mul_q(A: Sequence[Sequence[Fraction]], B: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    n = len(A)
    out = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        row_i = A[i]
        out_i = out[i]
        for k in range(n):
            aik = row_i[k]
            if aik == 0:
                continue
            row_k = B[k]
            for j in range(n):
                bkj = row_k[j]
                if bkj != 0:
                    out_i[j] += aik * bkj
    return out


def mat_pow_q(A: Sequence[Sequence[Fraction]], exp: int) -> List[List[Fraction]]:
    n = len(A)
    res = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    base = [list(row) for row in A]
    e = exp
    while e > 0:
        if e & 1:
            res = mat_mul_q(res, base)
        e >>= 1
        if e > 0:
            base = mat_mul_q(base, base)
    return res


def mat_mul_z(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> List[List[int]]:
    n = len(A)
    out = [[0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        row_i = A[i]
        out_i = out[i]
        for k in range(n):
            aik = row_i[k]
            if aik == 0:
                continue
            row_k = B[k]
            for j in range(n):
                bkj = row_k[j]
                if bkj != 0:
                    out_i[j] += aik * bkj
    return out


def adjacency_matrix_z(n: int, edges: Sequence[Tuple[int, int]]) -> List[List[int]]:
    A = [[0] * n for _ in range(n)]
    for u, v in edges:
        A[u][v] = 1
        A[v][u] = 1
    return A


def exact_cut_edges(edges: Sequence[Tuple[int, int]], S: Set[int], T: Set[int]) -> int:
    """Count undirected edges with one endpoint in S and the other in T (S, T disjoint)."""
    cnt = 0
    for u, v in edges:
        if (u in S and v in T) or (v in S and u in T):
            cnt += 1
    return cnt


def exact_edge_expansion(verts: Sequence[int], edges: Sequence[Tuple[int, int]]) -> Fraction:
    """Exact edge expansion h(G[verts]) = min_{0 < |S| <= |verts|/2} |E(S, verts\\S)| / |S| over Q."""
    m = len(verts)
    if m <= 1:
        raise ValueError("Edge expansion requires at least 2 vertices")
    vset = set(verts)
    sub_edges = [(u, v) for (u, v) in edges if u in vset and v in vset]
    best: Fraction | None = None
    for mask in range(1, (1 << m) - 1):
        sz = mask.bit_count()
        if sz > m // 2:
            continue
        S = {verts[i] for i in range(m) if (mask >> i) & 1}
        T = vset - S
        cut = exact_cut_edges(sub_edges, S, T)
        ratio = Fraction(cut, sz)
        if best is None or ratio < best:
            best = ratio
    assert best is not None
    return best


def exact_trimming_maximizer(
    H: Sequence[int],
    edges: Sequence[Tuple[int, int]],
    alpha: Fraction,
) -> Tuple[List[int], Fraction]:
    """Find exact maximizer R subseteq H, |R| <= |H|/2 of F(R) = alpha*|R| - |E(R, H\\R)| (Lem. 5.3)."""
    m = len(H)
    hset = set(H)
    sub_edges = [(u, v) for (u, v) in edges if u in hset and v in hset]
    best_R: List[int] = []
    best_val = Fraction(0)
    for mask in range(0, 1 << m):
        sz = mask.bit_count()
        if sz > m // 2:
            continue
        R = [H[i] for i in range(m) if (mask >> i) & 1]
        Rset = set(R)
        cut = exact_cut_edges(sub_edges, Rset, hset - Rset)
        val = alpha * sz - cut
        if val > best_val or (val == best_val and len(R) < len(best_R)):
            best_val = val
            best_R = R
    return best_R, best_val


def nonbacktracking_poly_matrix(A: Sequence[Sequence[int]], d: int, k: int) -> List[List[int]]:
    """Compute exact integer matrix Q_k(A) via Q_0=I, Q_1=A, Q_2=A^2-dI, Q_k=A Q_{k-1} - (d-1) Q_{k-2}."""
    n = len(A)
    Q0 = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    if k == 0:
        return Q0
    Q1 = [list(row) for row in A]
    if k == 1:
        return Q1
    A2 = mat_mul_z(A, A)
    Q2 = [[A2[i][j] - (d if i == j else 0) for j in range(n)] for i in range(n)]
    if k == 2:
        return Q2
    prev2, prev1 = Q1, Q2
    p = d - 1
    for _ in range(3, k + 1):
        AP = mat_mul_z(A, prev1)
        cur = [[AP[i][j] - p * prev2[i][j] for j in range(n)] for i in range(n)]
        prev2, prev1 = prev1, cur
    return prev1


def exact_r3(N: int) -> int:
    """Exact count r_3(N) = |{(x1,x2,x3) in Z^3 : x1^2 + x2^2 + x3^2 = N}|."""
    if N < 0:
        return 0
    if N == 0:
        return 1
    # Pure-integer isqrt
    r = 0
    while (r + 1) * (r + 1) <= N:
        r += 1
    cnt = 0
    for x1 in range(-r, r + 1):
        rem1 = N - x1 * x1
        for x2 in range(-r, r + 1):
            rem2 = rem1 - x2 * x2
            if rem2 < 0:
                continue
            # Check if rem2 is a perfect square
            lo, hi = 0, r
            found = -1
            while lo <= hi:
                mid = (lo + hi) // 2
                sq = mid * mid
                if sq == rem2:
                    found = mid
                    break
                elif sq < rem2:
                    lo = mid + 1
                else:
                    hi = mid - 1
            if found == 0:
                cnt += 1
            elif found > 0:
                cnt += 2
    return cnt
