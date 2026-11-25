"""Exact zero-floating-point four-mode certificate verifier for EXP-RETPROB-CERT-1.0.

Verifies exact lazy-walk return probabilities, good-vertex local conditions, induced-expander
trimming, balanced-cut farness, non-backtracking polynomials, and three-squares scaling for:
  Nikolas Melissaris, "Testing Expansion without Connectivity via Return Probabilities"
  (arXiv:2611.32677, Nov 24, 2026).

Strictly zero floating-point operations (uses int and fractions.Fraction exclusively).
Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from fractions import Fraction
import re
from typing import Any, Dict, List, Optional, Set, Tuple

from src.expansion_exact import (
    adjacency_matrix_z,
    build_lazy_walk_matrix,
    exact_cut_edges,
    exact_edge_expansion,
    exact_r3,
    exact_trimming_maximizer,
    frac_to_canon_str,
    int_gcd,
    mat_pow_q,
    nonbacktracking_poly_matrix,
)

SCHEMA_VERSION = "EXP-RETPROB-CERT-1.0"
MAX_BIT_LEN = 2048
MAX_JSON_DEPTH = 32
MAX_ID_LEN = 128

_CANON_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z")
_CANON_FRAC_RE = re.compile(r"\A(-?[1-9][0-9]*)/([1-9][0-9]*)\Z")

VALID_MODES = {
    "good_vertex_return_cert",
    "induced_expander_trim_cert",
    "balanced_cut_farness_cert",
    "nonbacktracking_and_walkreg_cert",
}


class CertError(ValueError):
    """Raised when a certificate violates schema, typing, or mathematical invariants."""


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


def _parse_canon_rat(v: Any, label: str) -> Fraction:
    if type(v) is not str or not v or len(v) > 512:
        raise CertError(f"{label}: expected canonical rational string")
    if _CANON_INT_RE.match(v):
        n = int(v)
        if n.bit_length() > MAX_BIT_LEN:
            raise CertError(f"{label}: rational numerator exceeds {MAX_BIT_LEN} bits")
        return Fraction(n, 1)
    m = _CANON_FRAC_RE.match(v)
    if m:
        p = int(m.group(1))
        q = int(m.group(2))
        if q <= 1:
            raise CertError(f"{label}: non-canonical denominator {q} (integers must omit /1)")
        if p.bit_length() > MAX_BIT_LEN or q.bit_length() > MAX_BIT_LEN:
            raise CertError(f"{label}: rational exceeds {MAX_BIT_LEN} bits")
        if int_gcd(p, q) != 1:
            raise CertError(f"{label}: non-reduced fraction {v!r}")
        return Fraction(p, q)
    raise CertError(f"{label}: malformed canonical rational string {v!r}")


def _parse_graph(raw_n: Any, raw_d: Any, raw_edges: Any, max_n: int = 16) -> Tuple[int, int, List[Tuple[int, int]]]:
    n = _parse_int(raw_n, "n", 2, max_n)
    d = _parse_int(raw_d, "d", 1, max_n)
    if type(raw_edges) is not list:
        raise CertError("edges: expected list of [u, v] pairs")
    seen: Set[Tuple[int, int]] = set()
    deg = [0] * n
    edges: List[Tuple[int, int]] = []
    for idx, e in enumerate(raw_edges):
        if type(e) is not list or len(e) != 2:
            raise CertError(f"edges[{idx}]: expected [u, v]")
        u = _parse_int(e[0], f"edges[{idx}][0]", 0, n - 1)
        v = _parse_int(e[1], f"edges[{idx}][1]", 0, n - 1)
        if u == v:
            raise CertError(f"edges[{idx}]: self-loop disallowed")
        pair = (u, v) if u < v else (v, u)
        if pair in seen:
            raise CertError(f"edges[{idx}]: duplicate edge {pair}")
        seen.add(pair)
        deg[u] += 1
        deg[v] += 1
        if deg[u] > d or deg[v] > d:
            raise CertError(f"edges[{idx}]: vertex degree exceeds bound d={d}")
        edges.append(pair)
    return n, d, edges


def _parse_int_set_list(v: Any, label: str, n: int, min_len: int = 0) -> List[int]:
    if type(v) is not list or len(v) < min_len or len(v) > n:
        raise CertError(f"{label}: expected list of {min_len}..{n} vertex indices")
    out = [_parse_int(x, f"{label}[{i}]", 0, n - 1) for i, x in enumerate(v)]
    if len(set(out)) != len(out):
        raise CertError(f"{label}: duplicate vertex index")
    if out != sorted(out):
        raise CertError(f"{label}: vertex indices must be strictly sorted ascending")
    return out


def _verify_mode1(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Sec. 2.1, 2.2, Lem. 5.1 exact lazy-walk return probabilities, D_s, H_s, & trace."""
    _require_exact_keys(
        payload,
        {
            "n",
            "d",
            "edges",
            "start_s",
            "walk_t",
            "eta",
            "claimed_A_s",
            "claimed_B_s",
            "claimed_D_s",
            "claimed_J_s",
            "claimed_is_good",
            "claimed_H_s",
            "claimed_dirichlet_energy",
            "claimed_tv_to_uniform_H_s",
            "claimed_boundary_H_s",
            "claimed_trace_K_2t",
        },
        "mode1.payload",
    )
    n, d, edges = _parse_graph(payload["n"], payload["d"], payload["edges"], max_n=14)
    s = _parse_int(payload["start_s"], "start_s", 0, n - 1)
    t = _parse_int(payload["walk_t"], "walk_t", 1, 5)
    eta = _parse_canon_rat(payload["eta"], "eta")
    if not (Fraction(0) < eta < Fraction(1, 2)):
        raise CertError("eta must lie strictly in (0, 1/2)")

    P = build_lazy_walk_matrix(n, d, edges)
    Pt = mat_pow_q(P, t)
    P2t = mat_pow_q(Pt, 2)
    P4t = mat_pow_q(P2t, 2)

    A_vec = [P2t[v][v] for v in range(n)]
    A_s = A_vec[s]
    p_s = P2t[s]
    B_s = P4t[s][s]

    # Exact Eq. (1) & (2) verification: A_s = ||P^t(s,.)||_2^2, B_s = ||p_s||_2^2, p_s(v)^2 <= A_s A_v
    if sum((Pt[s][v] * Pt[s][v] for v in range(n)), Fraction(0)) != A_s:
        raise CertError("Internal identity A_s != ||P^t(s,.)||_2^2")
    if sum((p_s[v] * p_s[v] for v in range(n)), Fraction(0)) != B_s:
        raise CertError("Internal identity B_s != ||p_s||_2^2")
    if not (Fraction(1, n) <= B_s <= A_s <= Fraction(1)):
        raise CertError("Eq. (7) violation: 1/n <= B_s <= A_s <= 1 failed")
    for v in range(n):
        if p_s[v] * p_s[v] > A_s * A_vec[v]:
            raise CertError(f"Eq. (2) Cauchy-Schwarz violated at vertex {v}")

    # Exact Dirichlet energy <= A_s - B_s (Lem. 5.1 p. 11)
    dir_energy = Fraction(1, 2 * d) * sum(((p_s[u] - p_s[v]) ** 2 for u, v in edges), Fraction(0))
    if dir_energy > A_s - B_s:
        raise CertError("Lem. 5.1 Dirichlet energy inequality violated")

    # Exact D_s, J_s, good-start predicate Eq. (4), H_s
    thresh_D = (Fraction(1) + 8 * eta) * A_s
    D_s = [v for v in range(n) if A_vec[v] > thresh_D]
    J_s = sum((p_s[v] * p_s[v] for v in D_s), Fraction(0))
    is_good = (A_s <= (Fraction(1) + 2 * eta) * B_s) and (J_s <= eta * B_s)

    D_set = set(D_s)
    H_s = [v for v in range(n) if p_s[v] >= Fraction(3, 4) * B_s and v not in D_set]
    if not H_s:
        raise CertError("H_s unexpectedly empty")

    # TV distance to uniform on H_s
    m_H = len(H_s)
    H_set = set(H_s)
    tv_sum = Fraction(0)
    for v in range(n):
        u_v = Fraction(1, m_H) if v in H_set else Fraction(0)
        tv_sum += abs(p_s[v] - u_v)
    tv_dist = tv_sum / 2

    bnd_H = exact_cut_edges(edges, H_set, set(range(n)) - H_set)

    # Restricted submatrix K_s = P[H_s, H_s] and exact trace tr(K_s^{2t}) <= sum_{v in H_s} A_v
    K_s = [[P[u][v] for v in H_s] for u in H_s]
    K_2t = mat_pow_q(K_s, 2 * t)
    tr_K = sum((K_2t[i][i] for i in range(m_H)), Fraction(0))
    sum_Av = sum((A_vec[v] for v in H_s), Fraction(0))
    if tr_K > sum_Av:
        raise CertError("Lem. 5.1 trace bound tr(K_s^{2t}) <= sum_{v in H_s} A_v violated")

    if _parse_canon_rat(payload["claimed_A_s"], "claimed_A_s") != A_s:
        raise CertError("claimed_A_s mismatch")
    if _parse_canon_rat(payload["claimed_B_s"], "claimed_B_s") != B_s:
        raise CertError("claimed_B_s mismatch")
    if _parse_int_set_list(payload["claimed_D_s"], "claimed_D_s", n, 0) != D_s:
        raise CertError("claimed_D_s mismatch")
    if _parse_canon_rat(payload["claimed_J_s"], "claimed_J_s") != J_s:
        raise CertError("claimed_J_s mismatch")
    if _parse_bool(payload["claimed_is_good"], "claimed_is_good") != is_good:
        raise CertError("claimed_is_good mismatch")
    if _parse_int_set_list(payload["claimed_H_s"], "claimed_H_s", n, 1) != H_s:
        raise CertError("claimed_H_s mismatch")
    if _parse_canon_rat(payload["claimed_dirichlet_energy"], "claimed_dirichlet_energy") != dir_energy:
        raise CertError("claimed_dirichlet_energy mismatch")
    if _parse_canon_rat(payload["claimed_tv_to_uniform_H_s"], "claimed_tv_to_uniform_H_s") != tv_dist:
        raise CertError("claimed_tv_to_uniform_H_s mismatch")
    if _parse_int(payload["claimed_boundary_H_s"], "claimed_boundary_H_s", 0) != bnd_H:
        raise CertError("claimed_boundary_H_s mismatch")
    if _parse_canon_rat(payload["claimed_trace_K_2t"], "claimed_trace_K_2t") != tr_K:
        raise CertError("claimed_trace_K_2t mismatch")

    return {
        "n": n,
        "t": t,
        "is_good": is_good,
        "H_size": m_H,
        "D_size": len(D_s),
        "boundary_H_s": bnd_H,
    }


def _verify_mode2(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Lem. 5.3 exact induced-expander trimming maximizer R of F(R) = (h/4)|R| - |E(R, H\\R)|."""
    _require_exact_keys(
        payload,
        {
            "n",
            "d",
            "edges",
            "H",
            "h_bound",
            "claimed_boundary_H",
            "claimed_tau",
            "claimed_R_maximizer",
            "claimed_F_max",
            "claimed_U",
            "claimed_induced_expansion_U",
            "claimed_boundary_U",
        },
        "mode2.payload",
    )
    n, d, edges = _parse_graph(payload["n"], payload["d"], payload["edges"], max_n=14)
    H = _parse_int_set_list(payload["H"], "H", n, 2)
    h_bound = _parse_canon_rat(payload["h_bound"], "h_bound")
    if not (Fraction(0) < h_bound <= Fraction(d)):
        raise CertError("h_bound must lie in (0, d]")

    m = len(H)
    H_set = set(H)
    V_all = set(range(n))

    # Exhaustively verify Lemma 5.3 hypothesis: every S subseteq H, |S| <= m/2 has |E(S, V\S)| >= h*|S|
    for mask in range(1, 1 << m):
        sz = mask.bit_count()
        if sz > m // 2:
            continue
        S = {H[i] for i in range(m) if (mask >> i) & 1}
        cut_G = exact_cut_edges(edges, S, V_all - S)
        if Fraction(cut_G, sz) < h_bound:
            raise CertError(f"Lem. 5.3 hypothesis violated: subset of size {sz} has cut {cut_G} < {h_bound}*{sz}")

    bnd_H = exact_cut_edges(edges, H_set, V_all - H_set)
    tau = Fraction(bnd_H, m)

    alpha = h_bound / 4
    R_star, F_max = exact_trimming_maximizer(H, edges, alpha)
    if F_max < 0:
        raise CertError("F(R_star) < 0 violates F(empty)=0")
    if Fraction(len(R_star), 1) > Fraction(4, 3) * (tau / h_bound) * m:
        raise CertError("Lem. 5.3 size bound |R| <= (4*tau/(3*h))*m violated")

    U = [v for v in H if v not in set(R_star)]
    if len(U) < 2:
        raise CertError("Trimmed set U has fewer than 2 vertices")
    h_U = exact_edge_expansion(U, edges)
    if h_U < alpha:
        raise CertError(f"Lem. 5.3 induced expansion violated: h(G[U])={h_U} < h/4={alpha}")
    bnd_U = exact_cut_edges(edges, set(U), V_all - set(U))

    if _parse_int(payload["claimed_boundary_H"], "claimed_boundary_H", 0) != bnd_H:
        raise CertError("claimed_boundary_H mismatch")
    if _parse_canon_rat(payload["claimed_tau"], "claimed_tau") != tau:
        raise CertError("claimed_tau mismatch")
    if _parse_int_set_list(payload["claimed_R_maximizer"], "claimed_R_maximizer", n, 0) != R_star:
        raise CertError("claimed_R_maximizer mismatch")
    if _parse_canon_rat(payload["claimed_F_max"], "claimed_F_max") != F_max:
        raise CertError("claimed_F_max mismatch")
    if _parse_int_set_list(payload["claimed_U"], "claimed_U", n, 2) != U:
        raise CertError("claimed_U mismatch")
    if _parse_canon_rat(payload["claimed_induced_expansion_U"], "claimed_induced_expansion_U") != h_U:
        raise CertError("claimed_induced_expansion_U mismatch")
    if _parse_int(payload["claimed_boundary_U"], "claimed_boundary_U", 0) != bnd_U:
        raise CertError("claimed_boundary_U mismatch")

    return {
        "H_size": m,
        "R_size": len(R_star),
        "U_size": len(U),
        "induced_expansion_U": frac_to_canon_str(h_U),
        "boundary_U": bnd_U,
    }


def _verify_mode3(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Lem. 7.3 exact farness lower bound from a sparse balanced cut on a connected expander."""
    _require_exact_keys(
        payload,
        {
            "n",
            "d",
            "edges",
            "cut_A",
            "target_c_star",
            "claimed_h0",
            "claimed_h1",
            "claimed_M_lower_bound",
            "claimed_eps0_lower_bound",
        },
        "mode3.payload",
    )
    n, d, edges = _parse_graph(payload["n"], payload["d"], payload["edges"], max_n=14)
    A = _parse_int_set_list(payload["cut_A"], "cut_A", n, 1)
    if len(A) > n // 2:
        raise CertError("cut_A must satisfy |A| <= n/2")
    c_star = _parse_canon_rat(payload["target_c_star"], "target_c_star")
    if c_star <= 0:
        raise CertError("target_c_star must be strictly positive")

    h0 = exact_edge_expansion(list(range(n)), edges)
    if h0 <= 0:
        raise CertError("Lem. 7.3 requires a connected graph (h(G) > 0)")

    A_set = set(A)
    cut_A = exact_cut_edges(edges, A_set, set(range(n)) - A_set)
    h1 = Fraction(cut_A, len(A))
    if h1 >= c_star:
        raise CertError(f"Lem. 7.3 requires h1 < c_star (got h1={h1}, c_star={c_star})")

    # Exact Lemma 7.3 trade-off bound across all three regimes (all comp <= n/2, s > |A|, s <= |A|)
    M_case1 = h0 * Fraction(n, 2)
    M_case2 = h0 * len(A)
    M_case3 = (h0 * (c_star - h1) / (h0 + c_star)) * len(A)
    M_lb = min(M_case1, M_case2, M_case3)
    eps0_lb = M_lb / (2 * d * n)

    if _parse_canon_rat(payload["claimed_h0"], "claimed_h0") != h0:
        raise CertError("claimed_h0 mismatch")
    if _parse_canon_rat(payload["claimed_h1"], "claimed_h1") != h1:
        raise CertError("claimed_h1 mismatch")
    if _parse_canon_rat(payload["claimed_M_lower_bound"], "claimed_M_lower_bound") != M_lb:
        raise CertError("claimed_M_lower_bound mismatch")
    if _parse_canon_rat(payload["claimed_eps0_lower_bound"], "claimed_eps0_lower_bound") != eps0_lb:
        raise CertError("claimed_eps0_lower_bound mismatch")

    return {
        "n": n,
        "h0": frac_to_canon_str(h0),
        "h1": frac_to_canon_str(h1),
        "M_lb": frac_to_canon_str(M_lb),
        "eps0_lb": frac_to_canon_str(eps0_lb),
    }


def _verify_mode4(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Lem. 7.5 non-backtracking polynomials Q_k(A), walk-regularity, & Lem. 7.4 r_3(4N)=r_3(N)."""
    if type(payload) is not dict or "submode" not in payload:
        raise CertError("mode4.payload: missing submode")
    submode = _parse_id_str(payload["submode"], "submode")

    if submode == "nonbacktracking_lps_poly":
        _require_exact_keys(
            payload,
            {
                "submode",
                "n",
                "d",
                "edges",
                "walk_k",
                "claimed_row_sum_Qk",
                "claimed_trace_Qk",
                "claimed_return_prob_Rk",
                "claimed_is_walk_regular_up_to_k",
            },
            "mode4.nonbacktracking_lps_poly",
        )
        n, d, edges = _parse_graph(payload["n"], payload["d"], payload["edges"], max_n=16)
        if d < 2:
            raise CertError("d must be >= 2 for non-backtracking walks")
        k = _parse_int(payload["walk_k"], "walk_k", 1, 6)

        A = adjacency_matrix_z(n, edges)
        for v in range(n):
            if sum(A[v]) != d:
                raise CertError(f"Graph is not {d}-regular at vertex {v}")

        Qk = nonbacktracking_poly_matrix(A, d, k)
        expected_row_sum = d * ((d - 1) ** (k - 1))
        for v in range(n):
            if sum(Qk[v]) != expected_row_sum:
                raise CertError(f"Q_{k}(A) row sum at vertex {v} != d(d-1)^(k-1)")

        tr_Qk = sum(Qk[v][v] for v in range(n))
        R_k = Fraction(tr_Qk, n * expected_row_sum)

        walk_reg = True
        for j in range(1, k + 1):
            Qj = nonbacktracking_poly_matrix(A, d, j)
            diag_vals = {Qj[v][v] for v in range(n)}
            if len(diag_vals) != 1:
                walk_reg = False
                break

        if _parse_int(payload["claimed_row_sum_Qk"], "claimed_row_sum_Qk", 1) != expected_row_sum:
            raise CertError("claimed_row_sum_Qk mismatch")
        if _parse_int(payload["claimed_trace_Qk"], "claimed_trace_Qk", 0) != tr_Qk:
            raise CertError("claimed_trace_Qk mismatch")
        if _parse_canon_rat(payload["claimed_return_prob_Rk"], "claimed_return_prob_Rk") != R_k:
            raise CertError("claimed_return_prob_Rk mismatch")
        if _parse_bool(payload["claimed_is_walk_regular_up_to_k"], "claimed_is_walk_regular_up_to_k") != walk_reg:
            raise CertError("claimed_is_walk_regular_up_to_k mismatch")

        return {
            "submode": submode,
            "n": n,
            "d": d,
            "k": k,
            "trace_Qk": tr_Qk,
            "R_k": frac_to_canon_str(R_k),
            "walk_regular": walk_reg,
        }

    if submode == "three_squares_and_collision_ambiguity":
        _require_exact_keys(
            payload,
            {
                "submode",
                "N_value",
                "claimed_r3_N",
                "claimed_r3_4N",
                "dist_p",
                "dist_q",
                "claimed_F2_common",
                "claimed_F3_p",
                "claimed_F3_q",
            },
            "mode4.three_squares_and_collision_ambiguity",
        )
        N = _parse_int(payload["N_value"], "N_value", 1, 60)
        rN = exact_r3(N)
        r4N = exact_r3(4 * N)
        if rN != r4N:
            raise CertError("Gauss identity r_3(4N) == r_3(N) violated")

        def _parse_dist(raw: Any, label: str) -> List[Fraction]:
            if type(raw) is not list or not (2 <= len(raw) <= 16):
                raise CertError(f"{label}: expected distribution list of length 2..16")
            probs = [_parse_canon_rat(x, f"{label}[{i}]") for i, x in enumerate(raw)]
            if any(p < 0 for p in probs) or sum(probs, Fraction(0)) != Fraction(1):
                raise CertError(f"{label}: must be nonnegative rationals summing to 1")
            return probs

        dp = _parse_dist(payload["dist_p"], "dist_p")
        dq = _parse_dist(payload["dist_q"], "dist_q")
        f2_p = sum((x * x for x in dp), Fraction(0))
        f2_q = sum((x * x for x in dq), Fraction(0))
        if f2_p != f2_q:
            raise CertError("dist_p and dist_q do not share collision probability F_2")
        f3_p = sum((x * x * x for x in dp), Fraction(0))
        f3_q = sum((x * x * x for x in dq), Fraction(0))
        if f3_p == f3_q:
            raise CertError("dist_p and dist_q must have distinct 3-way collision probability F_3")

        if _parse_int(payload["claimed_r3_N"], "claimed_r3_N", 0) != rN:
            raise CertError("claimed_r3_N mismatch")
        if _parse_int(payload["claimed_r3_4N"], "claimed_r3_4N", 0) != r4N:
            raise CertError("claimed_r3_4N mismatch")
        if _parse_canon_rat(payload["claimed_F2_common"], "claimed_F2_common") != f2_p:
            raise CertError("claimed_F2_common mismatch")
        if _parse_canon_rat(payload["claimed_F3_p"], "claimed_F3_p") != f3_p:
            raise CertError("claimed_F3_p mismatch")
        if _parse_canon_rat(payload["claimed_F3_q"], "claimed_F3_q") != f3_q:
            raise CertError("claimed_F3_q mismatch")

        return {
            "submode": submode,
            "N": N,
            "r3_N": rN,
            "F2_common": frac_to_canon_str(f2_p),
            "F3_gap": frac_to_canon_str(abs(f3_p - f3_q)),
        }

    raise CertError(f"unknown mode4 submode {submode!r}")


def verify_certificate(cert: Any) -> Tuple[bool, str, Dict[str, Any]]:
    """Verify an EXP-RETPROB-CERT-1.0 certificate payload with zero floating-point arithmetic."""
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

        if mode == "good_vertex_return_cert":
            summary = _verify_mode1(payload)
        elif mode == "induced_expander_trim_cert":
            summary = _verify_mode2(payload)
        elif mode == "balanced_cut_farness_cert":
            summary = _verify_mode3(payload)
        else:
            summary = _verify_mode4(payload)

        summary["cert_id"] = cert_id
        summary["mode"] = mode
        return True, "OK", summary
    except CertError as exc:
        return False, str(exc), {}
