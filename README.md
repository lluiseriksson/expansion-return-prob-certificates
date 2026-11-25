# Certified Verification of Expansion Testing without Connectivity via Lazy-Walk Return Probabilities

[![License: MIT](https://img.shields.io/badge/Code%20%26%20Lean-MIT-blue.svg)](LICENSE)
[![Paper License: CC-BY-4.0](https://img.shields.io/badge/Paper-CC--BY--4.0-green.svg)](paper/main.tex)

**Author:** Lluis Eriksson

Machine-checked **Lean 4.35.0** formalization and zero-floating-point exact $\mathbb{Q}/\mathbb{Z}$ certificate audit (`EXP-RETPROB-CERT-1.0`) for **Nikolas Melissaris** ([arXiv:2611.32677](https://arxiv.org/abs/2611.32677), Nov 24, 2026), *"Testing Expansion without Connectivity via Return Probabilities"*.

---

## Key Verified Artifacts

| Artifact | Verification Metric | Result |
| :--- | :--- | :--- |
| **Lean 4.35.0 Kernel** (`lean/ExpansionReturnProb.lean`) | 18 theorems, zero `sorry`, zero warnings, zero `Classical.choice` | **18 / 18 PASS** (`1` `none`, `1` `[propext]`, `16` `[propext, Quot.sound]`) |
| **Exact $\mathbb{Q}/\mathbb{Z}$ Verifier** (`src/expansion_certifier.py`) | Zero `float()`, `math.`, or `numpy`; 4-mode `EXP-RETPROB-CERT-1.0` | **16 / 16 PASS** (`0.180–2.195 ms`, total `14.53 ms`) |
| **Adversarial Red-Team Suite** (`tests/test_suite.py`) | 60 live forged payloads (12 global + 12/mode) | **60 / 60 REJECTED** |
| **SHA-256 Integrity Manifest** (`SHA256_MANIFEST.json`) | Full deterministic replay check (`scripts/verify_all.py`) | **39 / 39 MATCH** |
| **Manuscript** (`paper/main.pdf`) | 3 pages, 3 publication figures (`300 DPI`) | **0 warnings, 0 overfulls** |

---

## Four Certificate Modes (`EXP-RETPROB-CERT-1.0`)

1. **`good_vertex_return_cert` (Mode 1 — Sec. 2.1--2.2 & Lem. 5.1):** Constructs exact lazy walk $P = I - L_G/(2d)$ over $\mathbb{Q}$, verifies $A_s = P^{2t}(s,s)$, $B_s = P^{4t}(s,s)$, Cauchy--Schwarz $p_s(v)^2 \le A_s A_v$, Dirichlet energy $\le A_s - B_s$, heavy-return set $D_s$, good-start condition, nearly uniform set $H_s$, TV distance, boundary $|\partial H_s|$, and restricted trace $\mathrm{tr}(K_s^{2t}) \le \sum_{v \in H_s} A_v$.
2. **`induced_expander_trim_cert` (Mode 2 — Lem. 5.3):** Exhaustively checks $|E(S, V\setminus S)| \ge h|S|$ on all $S \subseteq H$ ($|S| \le |H|/2$), computes exact maximizer $R^*$ of $F(R) = \frac{h}{4}|R| - |E(R, H\setminus R)|$, checks $|R^*| \le \frac{4\tau}{3h}|H|$, and certifies exact induced expansion $h(G[H \setminus R^*]) \ge h/4$.
3. **`balanced_cut_farness_cert` (Mode 3 — Lem. 7.3):** Computes exact global edge expansion $h_0 = h(G) > 0$, balanced cut ratio $h_1 < c^*$, and exact rational edit and bounded-degree distance lower bounds $M_{\mathrm{lb}}$ and $\varepsilon_{\mathrm{lb}} = M_{\mathrm{lb}}/(2dn)$.
4. **`nonbacktracking_and_walkreg_cert` (Mode 4 — Lem. 7.4--7.5 & App. A):** Audits exact $d$-regular non-backtracking matrices $Q_k(A)$ (row sums $d(d-1)^{k-1}$, traces, return probabilities $R_G(k)$, walk-regularity) and Gauss's three-squares scaling $r_3(4N)=r_3(N)$ paired with equal-$F_2$, unequal-$F_3$ collision-ambiguity distributions.

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
- **AI Assistance Disclosure:** Prepared by sole author Lluis Eriksson with AI coding, formalization, and drafting assistance from Google Antigravity; all Lean proofs, exact rational/integer certificates, and adversarial tests were independently compiled and machine-verified locally.
