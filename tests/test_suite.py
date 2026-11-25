"""Live 60-attack adversarial red-team test suite for EXP-RETPROB-CERT-1.0.

Tests 12 global schema/typing/depth/control-char/canonical-rational attacks + 12 domain attacks per mode.
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

from src.expansion_certifier import verify_certificate


def _load(name: str) -> dict[str, Any]:
    return json.loads((ROOT / "certificates" / f"{name}.json").read_text(encoding="utf-8"))


def _mutate(cert: dict[str, Any], fn: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    c = copy.deepcopy(cert)
    fn(c)
    return c


def build_attacks() -> List[Tuple[str, str, Any]]:
    m1 = _load("m1_disjoint_2k4_good_start")
    m2 = _load("m2_trim_dangling_vertex_to_k5")
    m3 = _load("m3_farness_barbell_k4_1bridge")
    m4_nb = _load("m4_nb_poly_petersen_k5")
    m4_r3 = _load("m4_r3_scaling_and_sec1_ambiguity_n14")

    attacks: List[Tuple[str, str, Any]] = []

    # --- 12 Global Schema / Type / Depth / Control-Char / Canonical-Rational Attacks ---
    attacks.append(("global", "g01_wrong_schema_version", _mutate(m1, lambda c: c.__setitem__("schema_version", "EXP-RETPROB-CERT-2.0"))))
    attacks.append(("global", "g02_unknown_mode", _mutate(m1, lambda c: c.__setitem__("mode", "bogus_mode"))))
    attacks.append(("global", "g03_extra_top_key", _mutate(m1, lambda c: c.__setitem__("extra", 1))))
    attacks.append(("global", "g04_missing_payload_key", _mutate(m1, lambda c: c["payload"].pop("n"))))
    attacks.append(("global", "g05_raw_float_injected", _mutate(m1, lambda c: c["payload"].__setitem__("n", 8.0))))
    attacks.append(("global", "g06_bool_as_int_walk_t", _mutate(m1, lambda c: c["payload"].__setitem__("walk_t", True))))
    attacks.append(("global", "g07_int_as_bool_is_good", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_is_good", 1))))
    attacks.append(("global", "g08_nul_control_char_in_id", _mutate(m1, lambda c: c.__setitem__("cert_id", "bad\x00id"))))
    attacks.append(("global", "g09_neg_zero_canon_rat", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_J_s", "-0"))))
    attacks.append(("global", "g10_unreduced_canon_rat", _mutate(m1, lambda c: c["payload"].__setitem__("eta", "2/40"))))
    attacks.append(("global", "g11_excess_int_bits", _mutate(m4_nb, lambda c: c["payload"].__setitem__("claimed_trace_Qk", 1 << 2100))))

    def _deep_nest(c: dict[str, Any]) -> None:
        node: Any = "leaf"
        for _ in range(40):
            node = [node]
        c["payload"]["edges"] = node

    attacks.append(("global", "g12_excess_json_depth", _mutate(m1, _deep_nest)))

    # --- 12 Mode 1 Domain Attacks ---
    attacks.append(("mode1", "m1_01_self_loop_edge", _mutate(m1, lambda c: c["payload"]["edges"].append([0, 0]))))
    attacks.append(("mode1", "m1_02_duplicate_edge", _mutate(m1, lambda c: c["payload"]["edges"].append([0, 1]))))
    attacks.append(("mode1", "m1_03_degree_exceeds_d", _mutate(m1, lambda c: c["payload"].__setitem__("d", 2))))
    attacks.append(("mode1", "m1_04_eta_zero", _mutate(m1, lambda c: c["payload"].__setitem__("eta", "0"))))
    attacks.append(("mode1", "m1_05_wrong_A_s", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_A_s", "1/2"))))
    attacks.append(("mode1", "m1_06_wrong_B_s", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_B_s", "1/8"))))
    attacks.append(("mode1", "m1_07_wrong_is_good", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_is_good", False))))
    attacks.append(("mode1", "m1_08_wrong_H_s", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_H_s", [0, 1, 2]))))
    attacks.append(("mode1", "m1_09_unsorted_H_s", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_H_s", [3, 2, 1, 0]))))
    attacks.append(("mode1", "m1_10_wrong_dirichlet", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_dirichlet_energy", "1"))))
    attacks.append(("mode1", "m1_11_wrong_trace_K", _mutate(m1, lambda c: c["payload"].__setitem__("claimed_trace_K_2t", "1"))))
    attacks.append(("mode1", "m1_12_nonlist_edges_no_crash", _mutate(m1, lambda c: c["payload"].__setitem__("edges", "bad"))))

    # --- 12 Mode 2 Domain Attacks ---
    attacks.append(("mode2", "m2_01_h_bound_too_large", _mutate(m2, lambda c: c["payload"].__setitem__("h_bound", "4"))))
    attacks.append(("mode2", "m2_02_h_bound_zero", _mutate(m2, lambda c: c["payload"].__setitem__("h_bound", "0"))))
    attacks.append(("mode2", "m2_03_wrong_boundary_H", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_boundary_H", 1))))
    attacks.append(("mode2", "m2_04_wrong_tau", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_tau", "1"))))
    attacks.append(("mode2", "m2_05_wrong_R_maximizer", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_R_maximizer", []))))
    attacks.append(("mode2", "m2_06_wrong_F_max", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_F_max", "0"))))
    attacks.append(("mode2", "m2_07_wrong_U", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_U", [0, 1, 2, 3]))))
    attacks.append(("mode2", "m2_08_wrong_induced_exp", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_induced_expansion_U", "1"))))
    attacks.append(("mode2", "m2_09_wrong_boundary_U", _mutate(m2, lambda c: c["payload"].__setitem__("claimed_boundary_U", 9))))
    attacks.append(("mode2", "m2_10_duplicate_H_vertex", _mutate(m2, lambda c: c["payload"]["H"].append(0))))
    attacks.append(("mode2", "m2_11_singleton_H", _mutate(m2, lambda c: c["payload"].__setitem__("H", [0]))))
    attacks.append(("mode2", "m2_12_nonlist_H_no_crash", _mutate(m2, lambda c: c["payload"].__setitem__("H", 123))))

    # --- 12 Mode 3 Domain Attacks ---
    attacks.append(("mode3", "m3_01_disconnected_graph", _mutate(m3, lambda c: c["payload"]["edges"].pop())))
    attacks.append(("mode3", "m3_02_cut_A_exceeds_half", _mutate(m3, lambda c: c["payload"].__setitem__("cut_A", [0, 1, 2, 3, 4]))))
    attacks.append(("mode3", "m3_03_empty_cut_A", _mutate(m3, lambda c: c["payload"].__setitem__("cut_A", []))))
    attacks.append(("mode3", "m3_04_c_star_le_h1", _mutate(m3, lambda c: c["payload"].__setitem__("target_c_star", "1/4"))))
    attacks.append(("mode3", "m3_05_c_star_zero", _mutate(m3, lambda c: c["payload"].__setitem__("target_c_star", "0"))))
    attacks.append(("mode3", "m3_06_wrong_h0", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_h0", "1/2"))))
    attacks.append(("mode3", "m3_07_wrong_h1", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_h1", "1/2"))))
    attacks.append(("mode3", "m3_08_wrong_M_lb", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_M_lower_bound", "1"))))
    attacks.append(("mode3", "m3_09_wrong_eps0_lb", _mutate(m3, lambda c: c["payload"].__setitem__("claimed_eps0_lower_bound", "1/10"))))
    attacks.append(("mode3", "m3_10_unsorted_cut_A", _mutate(m3, lambda c: c["payload"].__setitem__("cut_A", [3, 2, 1, 0]))))
    attacks.append(("mode3", "m3_11_slash_one_rat", _mutate(m3, lambda c: c["payload"].__setitem__("target_c_star", "1/1"))))
    attacks.append(("mode3", "m3_12_nonlist_cut_A_no_crash", _mutate(m3, lambda c: c["payload"].__setitem__("cut_A", "0123"))))

    # --- 12 Mode 4 Domain Attacks ---
    attacks.append(("mode4", "m4_01_unknown_submode", _mutate(m4_nb, lambda c: c["payload"].__setitem__("submode", "bogus"))))
    attacks.append(("mode4", "m4_02_non_regular_graph", _mutate(m4_nb, lambda c: c["payload"]["edges"].pop())))
    attacks.append(("mode4", "m4_03_wrong_row_sum", _mutate(m4_nb, lambda c: c["payload"].__setitem__("claimed_row_sum_Qk", 47))))
    attacks.append(("mode4", "m4_04_wrong_trace_Qk", _mutate(m4_nb, lambda c: c["payload"].__setitem__("claimed_trace_Qk", 0))))
    attacks.append(("mode4", "m4_05_wrong_return_Rk", _mutate(m4_nb, lambda c: c["payload"].__setitem__("claimed_return_prob_Rk", "1/2"))))
    attacks.append(("mode4", "m4_06_wrong_walk_regular", _mutate(m4_nb, lambda c: c["payload"].__setitem__("claimed_is_walk_regular_up_to_k", False))))
    attacks.append(("mode4", "m4_07_r3_wrong_count", _mutate(m4_r3, lambda c: c["payload"].__setitem__("claimed_r3_N", 12))))
    attacks.append(("mode4", "m4_08_r3_wrong_4N", _mutate(m4_r3, lambda c: c["payload"].__setitem__("claimed_r3_4N", 24))))
    attacks.append(("mode4", "m4_09_dist_not_sum_one", _mutate(m4_r3, lambda c: c["payload"]["dist_p"].__setitem__(0, "1/3"))))
    attacks.append(("mode4", "m4_10_dist_mismatched_F2", _mutate(m4_r3, lambda c: c["payload"].__setitem__("dist_p", ["1/3", "2/3"]))))
    attacks.append(("mode4", "m4_11_dist_identical_F3", _mutate(m4_r3, lambda c: c["payload"].__setitem__("dist_q", ["1/2", "1/2"]))))
    attacks.append(("mode4", "m4_12_nonlist_dist_no_crash", _mutate(m4_r3, lambda c: c["payload"].__setitem__("dist_p", 123))))

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
