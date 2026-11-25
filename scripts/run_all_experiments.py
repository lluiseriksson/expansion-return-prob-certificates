"""Generate all 16 canonical EXP-RETPROB-CERT-1.0 certificates and 4 exact datasets.

Author: Lluis Eriksson
License: MIT
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.expansion_certifier import SCHEMA_VERSION, verify_certificate
from src.expansion_exact import (
    adjacency_matrix_z,
    build_lazy_walk_matrix,
    exact_cut_edges,
    exact_edge_expansion,
    exact_r3,
    exact_trimming_maximizer,
    frac_to_canon_str,
    mat_pow_q,
    nonbacktracking_poly_matrix,
)


def _write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def _clique_edges(offset: int, size: int) -> List[List[int]]:
    return [[offset + i, offset + j] for i in range(size) for j in range(i + 1, size)]


def _cycle_edges(n: int) -> List[List[int]]:
    return [[i, (i + 1) % n] for i in range(n)]


def _k33_edges() -> List[List[int]]:
    return [[i, 3 + j] for i in range(3) for j in range(3)]


def _cube_q3_edges() -> List[List[int]]:
    edges = []
    for u in range(8):
        for bit in range(3):
            v = u ^ (1 << bit)
            if u < v:
                edges.append([u, v])
    return edges


def _petersen_edges() -> List[List[int]]:
    edges = []
    for i in range(5):
        edges.append([i, (i + 1) % 5])
        edges.append([i, 5 + i])
        edges.append([5 + i, 5 + ((i + 2) % 5)])
    return sorted([min(u, v), max(u, v)] for u, v in edges)


def _make_mode1_cert(
    cert_id: str,
    ref: str,
    n: int,
    d: int,
    edges: List[List[int]],
    s: int,
    t: int,
    eta: Fraction,
) -> Dict[str, Any]:
    et = [(u, v) for u, v in edges]
    P = build_lazy_walk_matrix(n, d, et)
    P2t = mat_pow_q(P, 2 * t)
    P4t = mat_pow_q(P2t, 2)
    A_vec = [P2t[v][v] for v in range(n)]
    A_s = A_vec[s]
    p_s = P2t[s]
    B_s = P4t[s][s]
    D_s = [v for v in range(n) if A_vec[v] > (Fraction(1) + 8 * eta) * A_s]
    J_s = sum((p_s[v] * p_s[v] for v in D_s), Fraction(0))
    is_good = (A_s <= (Fraction(1) + 2 * eta) * B_s) and (J_s <= eta * B_s)
    H_s = [v for v in range(n) if p_s[v] >= Fraction(3, 4) * B_s and v not in set(D_s)]
    dir_e = Fraction(1, 2 * d) * sum(((p_s[u] - p_s[v]) ** 2 for u, v in et), Fraction(0))
    m_H = len(H_s)
    H_set = set(H_s)
    tv = sum((abs(p_s[v] - (Fraction(1, m_H) if v in H_set else Fraction(0))) for v in range(n)), Fraction(0)) / 2
    bnd = exact_cut_edges(et, H_set, set(range(n)) - H_set)
    K_s = [[P[u][v] for v in H_s] for u in H_s]
    K_2t = mat_pow_q(K_s, 2 * t)
    tr_K = sum((K_2t[i][i] for i in range(m_H)), Fraction(0))
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "good_vertex_return_cert",
        "reference": ref,
        "payload": {
            "n": n,
            "d": d,
            "edges": edges,
            "start_s": s,
            "walk_t": t,
            "eta": frac_to_canon_str(eta),
            "claimed_A_s": frac_to_canon_str(A_s),
            "claimed_B_s": frac_to_canon_str(B_s),
            "claimed_D_s": D_s,
            "claimed_J_s": frac_to_canon_str(J_s),
            "claimed_is_good": is_good,
            "claimed_H_s": H_s,
            "claimed_dirichlet_energy": frac_to_canon_str(dir_e),
            "claimed_tv_to_uniform_H_s": frac_to_canon_str(tv),
            "claimed_boundary_H_s": bnd,
            "claimed_trace_K_2t": frac_to_canon_str(tr_K),
        },
    }


def _make_mode2_cert(
    cert_id: str,
    ref: str,
    n: int,
    d: int,
    edges: List[List[int]],
    H: List[int],
    h_bound: Fraction,
) -> Dict[str, Any]:
    et = [(u, v) for u, v in edges]
    H_set = set(H)
    V_all = set(range(n))
    bnd_H = exact_cut_edges(et, H_set, V_all - H_set)
    tau = Fraction(bnd_H, len(H))
    R_star, F_max = exact_trimming_maximizer(H, et, h_bound / 4)
    U = [v for v in H if v not in set(R_star)]
    h_U = exact_edge_expansion(U, et)
    bnd_U = exact_cut_edges(et, set(U), V_all - set(U))
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "induced_expander_trim_cert",
        "reference": ref,
        "payload": {
            "n": n,
            "d": d,
            "edges": edges,
            "H": H,
            "h_bound": frac_to_canon_str(h_bound),
            "claimed_boundary_H": bnd_H,
            "claimed_tau": frac_to_canon_str(tau),
            "claimed_R_maximizer": R_star,
            "claimed_F_max": frac_to_canon_str(F_max),
            "claimed_U": U,
            "claimed_induced_expansion_U": frac_to_canon_str(h_U),
            "claimed_boundary_U": bnd_U,
        },
    }


def _make_mode3_cert(
    cert_id: str,
    ref: str,
    n: int,
    d: int,
    edges: List[List[int]],
    cut_A: List[int],
    c_star: Fraction,
) -> Dict[str, Any]:
    et = [(u, v) for u, v in edges]
    h0 = exact_edge_expansion(list(range(n)), et)
    cut_e = exact_cut_edges(et, set(cut_A), set(range(n)) - set(cut_A))
    h1 = Fraction(cut_e, len(cut_A))
    M_lb = min(h0 * Fraction(n, 2), h0 * len(cut_A), (h0 * (c_star - h1) / (h0 + c_star)) * len(cut_A))
    eps0_lb = M_lb / (2 * d * n)
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "balanced_cut_farness_cert",
        "reference": ref,
        "payload": {
            "n": n,
            "d": d,
            "edges": edges,
            "cut_A": cut_A,
            "target_c_star": frac_to_canon_str(c_star),
            "claimed_h0": frac_to_canon_str(h0),
            "claimed_h1": frac_to_canon_str(h1),
            "claimed_M_lower_bound": frac_to_canon_str(M_lb),
            "claimed_eps0_lower_bound": frac_to_canon_str(eps0_lb),
        },
    }


def _make_mode4_nb_cert(
    cert_id: str,
    ref: str,
    n: int,
    d: int,
    edges: List[List[int]],
    k: int,
) -> Dict[str, Any]:
    et = [(u, v) for u, v in edges]
    A = adjacency_matrix_z(n, et)
    Qk = nonbacktracking_poly_matrix(A, d, k)
    rsum = d * ((d - 1) ** (k - 1))
    tr_Qk = sum(Qk[v][v] for v in range(n))
    R_k = Fraction(tr_Qk, n * rsum)
    walk_reg = all(len({nonbacktracking_poly_matrix(A, d, j)[v][v] for v in range(n)}) == 1 for j in range(1, k + 1))
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "nonbacktracking_and_walkreg_cert",
        "reference": ref,
        "payload": {
            "submode": "nonbacktracking_lps_poly",
            "n": n,
            "d": d,
            "edges": edges,
            "walk_k": k,
            "claimed_row_sum_Qk": rsum,
            "claimed_trace_Qk": tr_Qk,
            "claimed_return_prob_Rk": frac_to_canon_str(R_k),
            "claimed_is_walk_regular_up_to_k": walk_reg,
        },
    }


def _make_mode4_r3_cert(
    cert_id: str,
    ref: str,
    N: int,
    dp: List[Fraction],
    dq: List[Fraction],
) -> Dict[str, Any]:
    rN = exact_r3(N)
    f2 = sum((x * x for x in dp), Fraction(0))
    f3_p = sum((x * x * x for x in dp), Fraction(0))
    f3_q = sum((x * x * x for x in dq), Fraction(0))
    return {
        "schema_version": SCHEMA_VERSION,
        "cert_id": cert_id,
        "mode": "nonbacktracking_and_walkreg_cert",
        "reference": ref,
        "payload": {
            "submode": "three_squares_and_collision_ambiguity",
            "N_value": N,
            "claimed_r3_N": rN,
            "claimed_r3_4N": exact_r3(4 * N),
            "dist_p": [frac_to_canon_str(x) for x in dp],
            "dist_q": [frac_to_canon_str(x) for x in dq],
            "claimed_F2_common": frac_to_canon_str(f2),
            "claimed_F3_p": frac_to_canon_str(f3_p),
            "claimed_F3_q": frac_to_canon_str(f3_q),
        },
    }


def build_all_certificates() -> List[Tuple[str, Dict[str, Any]]]:
    certs: List[Tuple[str, Dict[str, Any]]] = []

    # --- Mode 1: Good-Vertex Return-Probability Certificates (4 certs) ---
    # 1. Disconnected K4 + K4 (two disjoint expanders! Start in first K4 -> GOOD!)
    e_2k4 = _clique_edges(0, 4) + _clique_edges(4, 4)
    certs.append((
        "m1_disjoint_2k4_good_start",
        _make_mode1_cert("m1_disjoint_2k4_good_start", "Melissaris arXiv:2611.32677 Sec. 1 & 2.1 (K4 + K4 good start)", 8, 4, e_2k4, 0, 3, Fraction(1, 20)),
    ))
    # 2. Disconnected K5 + K3 (asymmetric component sizes -> GOOD!)
    e_k5k3 = _clique_edges(0, 5) + _clique_edges(5, 3)
    certs.append((
        "m1_disjoint_k5_k3_asymmetric",
        _make_mode1_cert("m1_disjoint_k5_k3_asymmetric", "Melissaris arXiv:2611.32677 Lem. 5.1 (K5 + K3 unequal components)", 8, 4, e_k5k3, 0, 3, Fraction(1, 20)),
    ))
    # 3. Barbell K4 --bridge-- K4 (sparse bridge -> local mixing detected!)
    e_barbell = _clique_edges(0, 4) + _clique_edges(4, 4) + [[3, 4]]
    certs.append((
        "m1_barbell_k4_bridge_slow_cut",
        _make_mode1_cert("m1_barbell_k4_bridge_slow_cut", "Melissaris arXiv:2611.32677 Sec. 2.2 (K4-K4 bridge cut)", 8, 4, e_barbell, 0, 2, Fraction(1, 16)),
    ))
    # 4. Path P8 (non-expander -> BAD start detected via A_s > (1+2*eta)B_s!)
    e_p8 = [[i, i + 1] for i in range(7)]
    certs.append((
        "m1_path_p8_bad_start_rejected",
        _make_mode1_cert("m1_path_p8_bad_start_rejected", "Melissaris arXiv:2611.32677 Eq. (4) (Path P8 violates good condition)", 8, 3, e_p8, 3, 2, Fraction(1, 20)),
    ))

    # --- Mode 2: Lemma 5.3 Induced-Expander Trimming Certificates (4 certs) ---
    # 1. Clean K5 inside K5 + K3 with 1 bridge: R = empty, U = K5
    e_k5_b_k3 = _clique_edges(0, 5) + _clique_edges(5, 3) + [[4, 5]]
    certs.append((
        "m2_trim_clean_k5_no_removal",
        _make_mode2_cert("m2_trim_clean_k5_no_removal", "Melissaris arXiv:2611.32677 Lem. 5.3 (clean K5, R=empty)", 8, 5, e_k5_b_k3, [0, 1, 2, 3, 4], Fraction(2)),
    ))
    # 2. K5 + dangling leaf vertex 5 inside H={0..5}, where leaf 5 has 3 external edges to {6,7,8}:
    e_trim_leaf = _clique_edges(0, 5) + [[5, 6], [5, 7], [5, 8]] + _clique_edges(6, 3)
    certs.append((
        "m2_trim_dangling_vertex_to_k5",
        _make_mode2_cert("m2_trim_dangling_vertex_to_k5", "Melissaris arXiv:2611.32677 Lem. 5.3 (trims disconnected boundary vertex)", 9, 5, e_trim_leaf, [0, 1, 2, 3, 4, 5], Fraction(2)),
    ))
    # 3. K6 + boundary vertex 6 (0 internal edges to K6, 3 external edges to {7,8,9}) -> trims R=[6] to U=K6!
    e_trim_k6 = _clique_edges(0, 6) + [[6, 7], [6, 8], [6, 9]] + _clique_edges(7, 3)
    certs.append((
        "m2_trim_boundary_vertex_to_k6",
        _make_mode2_cert("m2_trim_boundary_vertex_to_k6", "Melissaris arXiv:2611.32677 Lem. 5.3 (trims boundary vertex from K6)", 10, 5, e_trim_k6, [0, 1, 2, 3, 4, 5, 6], Fraction(3)),
    ))
    # 4. K4 + 2-vertex external-heavy appendage {4,5} with 0 internal edges to K4 -> trims R={4,5} to U=K4!
    e_trim_pair = _clique_edges(0, 4) + [[4, 5], [4, 6], [4, 7], [5, 6], [5, 7]] + [[6, 7]]
    certs.append((
        "m2_trim_two_vertex_appendage",
        _make_mode2_cert("m2_trim_two_vertex_appendage", "Melissaris arXiv:2611.32677 Lem. 5.3 (trims 2-vertex appendage)", 8, 4, e_trim_pair, [0, 1, 2, 3, 4, 5], Fraction(1)),
    ))

    # --- Mode 3: Lemma 7.3 Balanced-Cut Farness Certificates (4 certs) ---
    # 1. Barbell K4 --1 edge-- K4 (n=8, d=4, h0=1/4, h1=1/4, c*=1)
    certs.append((
        "m3_farness_barbell_k4_1bridge",
        _make_mode3_cert("m3_farness_barbell_k4_1bridge", "Melissaris arXiv:2611.32677 Lem. 7.3 (K4-K4 1-bridge farness)", 8, 4, e_barbell, [0, 1, 2, 3], Fraction(1)),
    ))
    # 2. 2-bridge K5 == K5 (n=10, d=5, cut_A={0..4}, h1=2/5, c*=3/2)
    e_2k5_2b = _clique_edges(0, 5) + _clique_edges(5, 5) + [[0, 5], [1, 6]]
    certs.append((
        "m3_farness_k5_2bridge",
        _make_mode3_cert("m3_farness_k5_2bridge", "Melissaris arXiv:2611.32677 Lem. 7.3 (K5-K5 2-bridge farness)", 10, 5, e_2k5_2b, [0, 1, 2, 3, 4], Fraction(3, 2)),
    ))
    # 3. 3-cube Q3 (n=8, d=3, h0=1, face cut A={0,1,2,3} has h1=1, c*=2)
    certs.append((
        "m3_farness_hypercube_q3",
        _make_mode3_cert("m3_farness_hypercube_q3", "Melissaris arXiv:2611.32677 Lem. 7.3 (Hypercube Q3 balanced cut)", 8, 3, _cube_q3_edges(), [0, 1, 2, 3], Fraction(2)),
    ))
    # 4. Cyclic 3-ring of triangles C_3 x K_3-like (n=9, d=4, sparse cut A={0,1,2})
    e_ring3 = _clique_edges(0, 3) + _clique_edges(3, 3) + _clique_edges(6, 3) + [[0, 3], [3, 6], [6, 0], [1, 4], [4, 7], [7, 1]]
    certs.append((
        "m3_farness_cyclic_3block_lift",
        _make_mode3_cert("m3_farness_cyclic_3block_lift", "Melissaris arXiv:2611.32677 Lem. 7.2 & 7.3 (Cyclic Z_3 lift cut)", 9, 4, e_ring3, [0, 1, 2], Fraction(2)),
    ))

    # --- Mode 4: Lem. 7.5 Non-Backtracking Polynomials & Lem. 7.4 Three-Squares / Sec. 1 Ambiguity (4 certs) ---
    certs.append((
        "m4_nb_poly_petersen_k5",
        _make_mode4_nb_cert("m4_nb_poly_petersen_k5", "Melissaris arXiv:2611.32677 Lem. 7.5 (Petersen graph Q_5(A), girth=5)", 10, 3, _petersen_edges(), 5),
    ))
    certs.append((
        "m4_nb_poly_k33_bipartite_k4",
        _make_mode4_nb_cert("m4_nb_poly_k33_bipartite_k4", "Melissaris arXiv:2611.32677 Lem. 7.5 & App. A (Bipartite K_{3,3} Q_4(A))", 6, 3, _k33_edges(), 4),
    ))
    certs.append((
        "m4_r3_scaling_and_sec1_ambiguity_n14",
        _make_mode4_r3_cert(
            "m4_r3_scaling_and_sec1_ambiguity_n14",
            "Melissaris arXiv:2611.32677 Sec. 1 & Lem. 7.4 (r_3(56)=r_3(14) & F_2=1/2 ambiguity)",
            14,
            [Fraction(1, 2), Fraction(1, 2)],
            [Fraction(2, 3), Fraction(1, 6), Fraction(1, 6)],
        ),
    ))
    certs.append((
        "m4_r3_scaling_and_sec1_ambiguity_n27",
        _make_mode4_r3_cert(
            "m4_r3_scaling_and_sec1_ambiguity_n27",
            "Melissaris arXiv:2611.32677 Sec. 1 & Lem. 7.4 (r_3(108)=r_3(27) & F_2=1/3 ambiguity)",
            27,
            [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)],
            [Fraction(1, 2), Fraction(1, 6), Fraction(1, 6), Fraction(1, 6)],
        ),
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

    # Dataset 1: Exact return-probability ratio A_s / B_s vs walk length t=1..6 across 3 graphs (2K4, Barbell, Path P8)
    graphs = [
        ("2K4_expander", 8, 4, [(u, v) for u, v in _clique_edges(0, 4) + _clique_edges(4, 4)], 0),
        ("Barbell_K4", 8, 4, [(u, v) for u, v in _clique_edges(0, 4) + _clique_edges(4, 4) + [[3, 4]]], 0),
        ("Path_P8", 8, 3, [(i, i + 1) for i in range(7)], 3),
    ]
    exp1_rows = []
    for gname, n, d, et, s in graphs:
        P = build_lazy_walk_matrix(n, d, et)
        for t in range(1, 7):
            P2t = mat_pow_q(P, 2 * t)
            P4t = mat_pow_q(P2t, 2)
            A_s = P2t[s][s]
            B_s = P4t[s][s]
            ratio = A_s / B_s
            exp1_rows.append(
                {
                    "graph": gname,
                    "t": t,
                    "A_s": frac_to_canon_str(A_s),
                    "B_s": frac_to_canon_str(B_s),
                    "ratio_A_over_B": frac_to_canon_str(ratio),
                    "ratio_float_plot": ratio.numerator / ratio.denominator,
                }
            )
    _write_json(data_dir / "exp1_return_ratio_trajectory.json", {"rows": exp1_rows})

    # Dataset 2: Non-backtracking return probabilities R_G(k) for k=1..6 on Petersen (girth 5), Q3 (girth 4), K3,3 (girth 4)
    reg_graphs = [
        ("Petersen_n10_d3", 10, 3, [(u, v) for u, v in _petersen_edges()]),
        ("Hypercube_Q3_n8_d3", 8, 3, [(u, v) for u, v in _cube_q3_edges()]),
        ("Bipartite_K33_n6_d3", 6, 3, [(u, v) for u, v in _k33_edges()]),
    ]
    exp2_rows = []
    for gname, n, d, et in reg_graphs:
        A = adjacency_matrix_z(n, et)
        for k in range(1, 7):
            Qk = nonbacktracking_poly_matrix(A, d, k)
            tr = sum(Qk[v][v] for v in range(n))
            rsum = d * ((d - 1) ** (k - 1))
            Rk = Fraction(tr, n * rsum)
            exp2_rows.append(
                {
                    "graph": gname,
                    "k": k,
                    "trace_Qk": tr,
                    "R_k": frac_to_canon_str(Rk),
                    "R_k_plot": Rk.numerator / Rk.denominator,
                }
            )
    _write_json(data_dir / "exp2_nonbacktracking_returns.json", {"rows": exp2_rows})

    # Dataset 3: Exact r_3(N) = r_3(4N) for N=1..30 (Lemma 7.4)
    exp3_rows = []
    for N in range(1, 31):
        rN = exact_r3(N)
        r4N = exact_r3(4 * N)
        assert rN == r4N
        exp3_rows.append({"N": N, "r3_N": rN, "r3_4N": r4N, "matches": True})
    _write_json(data_dir / "exp3_three_squares_scaling.json", {"rows": exp3_rows})

    total_ms = sum(r["verify_ns"] for r in replay_rows) / 1_000_000
    min_ms = min(r["verify_ns"] for r in replay_rows) / 1_000_000
    max_ms = max(r["verify_ns"] for r in replay_rows) / 1_000_000
    print(f"Generated & verified 16/16 canonical EXP-RETPROB-CERT-1.0 certificates ({min_ms:.3f}-{max_ms:.3f} ms, total {total_ms:.2f} ms).")


if __name__ == "__main__":
    main()
