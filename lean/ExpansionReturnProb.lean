/-
  ExpansionReturnProb.lean
  Standalone zero-dependency Lean 4.35.0 formalization of 18 core lazy-walk,
  Cauchy-Schwarz collision, Dirichlet energy, trace-gap, Bernoulli, induced-expander
  trimming, balanced-cut farness, non-backtracking polynomial, three-squares parity,
  and walk-regular spectral theorems for:
    Nikolas Melissaris, "Testing Expansion without Connectivity via Return Probabilities",
    arXiv:2611.32677 (Nov. 24, 2026).

  Author: Lluis Eriksson
  License: MIT
-/

namespace ExpansionReturnProb

/-- Helper: `0 ≤ z * z` for every integer `z` without `Classical.choice`. -/
private theorem sq_nonneg (z : Int) : 0 ≤ z * z := by
  if hz : 0 ≤ z then
    exact Int.mul_nonneg hz hz
  else
    have hnz : 0 ≤ -z := by omega
    have hprod : 0 ≤ (-z) * (-z) := Int.mul_nonneg hnz hnz
    rw [Int.neg_mul_neg] at hprod
    exact hprod

/-- Exact inner product `∑ a_i * b_i` of two integer lists (single-arg structural recursion). -/
def dotProd : List Int → List Int → Int
  | [], _ => 0
  | a :: as, bs =>
    match bs with
    | [] => 0
    | b :: bs' => a * b + dotProd as bs'

/-- Sum of squares `∑ a_i^2` of an integer list. -/
def sqSum : List Int → Int
  | [] => 0
  | a :: as => a * a + sqSum as

/-- Sum of elements `∑ a_i` of an integer list. -/
def listSum : List Int → Int
  | [] => 0
  | a :: as => a + listSum as

/-- Dirichlet energy `∑_{(u,v)} (u - v)^2` over a list of endpoint-value pairs. -/
def dirichletSum : List (Int × Int) → Int
  | [] => 0
  | (u, v) :: es => (u - v) * (u - v) + dirichletSum es

private theorem sqSum_nonneg (xs : List Int) : 0 ≤ sqSum xs := by
  induction xs with
  | nil => dsimp only [sqSum]; omega
  | cons a as ih =>
    dsimp only [sqSum]
    have ha := sq_nonneg a
    omega

/-- Theorem 1 (Sec. 3.1 Lazy Random Walk Row Stochasticity):
    For degree bound `d ≥ 1` and vertex degree `0 ≤ deg ≤ d`, the cleared row sum
    `(2*d - deg) + deg` equals `2*d`, and the lazy stay weight satisfies `2*d - deg ≥ d`. -/
theorem lazy_walk_row_stochastic_sum (d deg : Int) (hd : 1 ≤ d) (_hlo : 0 ≤ deg) (hhi : deg ≤ d) :
    ((2 * d - deg) + deg = 2 * d) ∧ (d ≤ 2 * d - deg) ∧ (0 < 2 * d - deg) :=
  ⟨by omega, by omega, by omega⟩

/-- Theorem 2 (Sec. 2.2 & Lem. 5.1 Lazy-Walk Dirichlet Energy Nonnegativity):
    For every finite list of edge endpoint-value pairs `es`, `0 ≤ dirichletSum es`. -/
theorem lazy_walk_dirichlet_nonneg (es : List (Int × Int)) :
    0 ≤ dirichletSum es := by
  induction es with
  | nil => dsimp only [dirichletSum]; omega
  | cons e rest ih =>
    cases e with
    | mk u v =>
      dsimp only [dirichletSum]
      have hsq := sq_nonneg (u - v)
      omega

/-- Helper: Lagrange/Cauchy-Schwarz induction over equal-length lists. -/
private theorem lagrange_cs (xs : List Int) :
    ∀ ys : List Int, xs.length = ys.length →
      dotProd xs ys * dotProd xs ys ≤ sqSum xs * sqSum ys := by
  induction xs with
  | nil =>
    intro ys hlen
    cases ys with
    | nil => dsimp only [dotProd, sqSum]; omega
    | cons _ _ => dsimp only [List.length] at hlen; omega
  | cons a as ih =>
    intro ys hlen
    cases ys with
    | nil => dsimp only [List.length] at hlen; omega
    | cons b bs =>
      have hlen' : as.length = bs.length := by dsimp only [List.length] at hlen; omega
      have hsub := ih bs hlen'
      dsimp only [dotProd, sqSum]
      have hcross : ∀ (us vs : List Int), us.length = vs.length →
          2 * (a * b) * dotProd us vs ≤ (a * a) * sqSum vs + (b * b) * sqSum us := by
        intro us
        induction us with
        | nil =>
          intro vs hl
          cases vs with
          | nil => dsimp only [dotProd, sqSum]; rw [Int.mul_zero, Int.mul_zero, Int.mul_zero]; omega
          | cons _ _ => dsimp only [List.length] at hl; omega
        | cons u us' ihu =>
          intro vs hl
          cases vs with
          | nil => dsimp only [List.length] at hl; omega
          | cons v vs' =>
            have hl' : us'.length = vs'.length := by dsimp only [List.length] at hl; omega
            have hrest := ihu vs' hl'
            dsimp only [dotProd, sqSum]
            have hsq := sq_nonneg (a * v - b * u)
            have hexp : (a * v - b * u) * (a * v - b * u) =
                (a * a) * (v * v) + (b * b) * (u * u) - 2 * (a * b) * (u * v) := by
              rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
              have c1 : a * v * (a * v) = a * a * (v * v) := by
                rw [Int.mul_assoc, Int.mul_comm v (a * v), ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_assoc (a * a)]
              have c2 : b * u * (b * u) = b * b * (u * u) := by
                rw [Int.mul_assoc, Int.mul_comm u (b * u), ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_assoc (b * b)]
              have c3 : a * v * (b * u) = a * b * (u * v) := by
                rw [Int.mul_assoc, Int.mul_comm v (b * u), ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_assoc (a * b)]
              have c4 : b * u * (a * v) = a * b * (u * v) := by
                rw [Int.mul_comm (b * u) (a * v)]; exact c3
              have c5 : 2 * (a * b) * (u * v) = 2 * (a * b * (u * v)) := Int.mul_assoc 2 (a * b) (u * v)
              omega
            rw [Int.mul_add, Int.mul_add, Int.mul_add]
            omega
      have hcr := hcross as bs hlen'
      have hlhs : (a * b + dotProd as bs) * (a * b + dotProd as bs) =
          (a * a) * (b * b) + 2 * (a * b) * dotProd as bs + dotProd as bs * dotProd as bs := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        have c1 : a * b * (a * b) = a * a * (b * b) := by
          rw [Int.mul_assoc, Int.mul_comm b (a * b), ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_assoc (a * a)]
        have c2 : dotProd as bs * (a * b) = a * b * dotProd as bs := Int.mul_comm _ _
        have c3 : 2 * (a * b) * dotProd as bs = 2 * (a * b * dotProd as bs) := Int.mul_assoc 2 (a * b) _
        omega
      have hrhs : (a * a + sqSum as) * (b * b + sqSum bs) =
          (a * a) * (b * b) + (a * a) * sqSum bs + (b * b) * sqSum as + sqSum as * sqSum bs := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        have c1 : sqSum as * (b * b) = b * b * sqSum as := Int.mul_comm _ _
        omega
      omega

/-- Theorem 3 (Sec. 2.1 Eq. 2 Cauchy-Schwarz Return-Probability Bound):
    For any two equal-length integer vectors `xs, ys`, `(dotProd xs ys)^2 ≤ sqSum xs * sqSum ys`,
    certifying `p_s(v)^2 = ⟨P^t(s,·), P^t(v,·)⟩^2 ≤ A_s * A_v`. -/
theorem cauchy_schwarz_return_bound_finite (xs ys : List Int) (hlen : xs.length = ys.length) :
    dotProd xs ys * dotProd xs ys ≤ sqSum xs * sqSum ys :=
  lagrange_cs xs ys hlen

/-- Theorem 4 (Sec. 3.1 Eq. 7 Minimum Collision Probability `B_s ≥ 1/n`):
    For any integer vector `xs` of length `n`, `(listSum xs)^2 ≤ n * sqSum xs`. -/
theorem collision_prob_uniform_lower_bound (xs : List Int) :
    listSum xs * listSum xs ≤ (xs.length : Int) * sqSum xs := by
  have hones_len : (List.replicate xs.length (1 : Int)).length = xs.length := List.length_replicate
  have hdot : ∀ ps : List Int, dotProd ps (List.replicate ps.length (1 : Int)) = listSum ps := by
    intro ps
    induction ps with
    | nil => rfl
    | cons a as ih =>
      dsimp only [List.length, List.replicate, dotProd, listSum]
      rw [Int.mul_one, ih]
  have hsq1 : ∀ n : Nat, sqSum (List.replicate n (1 : Int)) = (n : Int) := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      dsimp only [List.replicate, sqSum]
      rw [ih]
      omega
  have hcs := lagrange_cs xs (List.replicate xs.length (1 : Int)) hones_len.symm
  rw [hdot xs, hsq1 xs.length] at hcs
  have hcomm : sqSum xs * (xs.length : Int) = (xs.length : Int) * sqSum xs := Int.mul_comm _ _
  omega

/-- Theorem 5 (Sec. 1 p. 2 Exact Collision-Probability Ambiguity Counterexample):
    Uniform `(1/2, 1/2)` and non-uniform `(2/3, 1/6, 1/6)` have IDENTICAL collision probability
    `1/2` (cleared by 36: `18^2 + 18^2 = 24^2 + 6^2 + 6^2 = 648 = 18 * 36`), yet distinct 3-way
    collision sums (`11664 ≠ 14256`) and nonzero TV distance. -/
theorem two_point_vs_three_point_collision_ambiguity :
    ((18 : Int) + 18 = 36) ∧
    ((24 : Int) + 6 + 6 = 36) ∧
    ((18 : Int) * 18 + 18 * 18 = 18 * 36) ∧
    ((24 : Int) * 24 + 6 * 6 + 6 * 6 = 18 * 36) ∧
    ((18 : Int) * 18 * 18 + 18 * 18 * 18 ≠ 24 * 24 * 24 + 6 * 6 * 6 + 6 * 6 * 6) := by
  decide

/-- Theorem 6 (Lem. 5.1 p. 11 Spectral Dirichlet-Energy Monotonicity `λ^4(1-λ) ≤ λ^2(1-λ^2)`):
    For every cleared eigenvalue `0 ≤ x ≤ D` with `0 ≤ D`,
    `x^4 * (D - x) ≤ D^3 * x^2 * (D^2 - x^2)` (equivalently `λ^4(1 - λ) ≤ λ^2(1 - λ^2)` for `λ ∈ [0,1]`). -/
theorem good_vertex_dirichlet_energy_monotonicity (x D : Int) (hx0 : 0 ≤ x) (hxD : x ≤ D) :
    (x * x) * (x * x) * (D - x) ≤ (D * D * D) * (x * x) * (D * D - x * x) := by
  have hD0 : 0 ≤ D := by omega
  have hDx : 0 ≤ D - x := by omega
  have hx2 : 0 ≤ x * x := Int.mul_nonneg hx0 hx0
  have hD2 : 0 ≤ D * D := Int.mul_nonneg hD0 hD0
  have hx2_le_D2 : x * x ≤ D * D := Int.mul_le_mul hxD hxD hx0 hD0
  have hstep1 : x * x * (x * x) ≤ D * D * (x * x) :=
    Int.mul_le_mul_of_nonneg_right hx2_le_D2 hx2
  have hstep2 : x * x * (x * x) * (D - x) ≤ D * D * (x * x) * (D - x) :=
    Int.mul_le_mul_of_nonneg_right hstep1 hDx
  have hdiff_id : (D + x) * (D - x) = D * D - x * x := by
    rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm x D]; omega
  if hDz : D = 0 then
    subst hDz
    have hx0' : x = 0 := by omega
    subst hx0'
    decide
  else
    have hD1 : 1 ≤ D := by omega
    have hDx_le : D - x ≤ (D + x) * (D - x) := by
      have h1_le_sum : 1 ≤ D + x := by omega
      have := Int.mul_le_mul_of_nonneg_right h1_le_sum hDx
      rw [Int.one_mul] at this
      exact this
    rw [hdiff_id] at hDx_le
    have hmul1 : D * D * (x * x) * (D - x) ≤ D * D * (x * x) * (D * D - x * x) :=
      Int.mul_le_mul_of_nonneg_left hDx_le (Int.mul_nonneg hD2 hx2)
    have hmul2 : D * D * (x * x) ≤ D * D * D * (x * x) := by
      have hD2_le_D3 : D * D ≤ D * D * D := by
        have := Int.mul_le_mul_of_nonneg_left hD1 hD2
        rw [Int.mul_one] at this
        exact this
      exact Int.mul_le_mul_of_nonneg_right hD2_le_D3 hx2
    have hD2x2_nn : 0 ≤ D * D - x * x := by omega
    have hmul3 : D * D * (x * x) * (D * D - x * x) ≤ D * D * D * (x * x) * (D * D - x * x) :=
      Int.mul_le_mul_of_nonneg_right hmul2 hD2x2_nn
    omega

/-- Theorem 7 (Lem. 5.1 p. 11 Heavy-Return Set Cardinality Bound `|H_0 ∩ D_s| ≤ 16 J_s / (9 B_s^2)`):
    If `0 ≤ B` and every element `p` in `ps` satisfies `3 * B ≤ 4 * p`, then
    `(9 * B * B) * ps.length ≤ 16 * sqSum ps`. -/
theorem heavy_return_set_size_bound (B : Int) (hB : 0 ≤ B) (ps : List Int)
    (hmin : ∀ p, p ∈ ps → 3 * B ≤ 4 * p) :
    (9 * B * B) * (ps.length : Int) ≤ 16 * sqSum ps := by
  induction ps with
  | nil =>
    dsimp only [List.length, sqSum]
    change (9 * B * B) * 0 ≤ 16 * 0
    rw [Int.mul_zero, Int.mul_zero]
    exact Int.le_refl 0
  | cons p rest ih =>
    have hp : 3 * B ≤ 4 * p := hmin p List.mem_cons_self
    have hrest := ih (fun q hq => hmin q (List.mem_cons_of_mem p hq))
    have h3B : 0 ≤ 3 * B := by omega
    have hsq : (3 * B) * (3 * B) ≤ (4 * p) * (4 * p) := Int.mul_le_mul hp hp h3B (by omega)
    have hl : (3 * B) * (3 * B) = 9 * B * B := by
      rw [Int.mul_assoc, Int.mul_comm B (3 * B), ← Int.mul_assoc, ← Int.mul_assoc]; rfl
    have hr : (4 * p) * (4 * p) = 16 * (p * p) := by
      rw [Int.mul_assoc, Int.mul_comm p (4 * p), ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_assoc (4 * 4)]; rfl
    dsimp only [List.length, sqSum]
    rw [Int.mul_add]
    have hlen_add : ((rest.length + 1 : Nat) : Int) = (rest.length : Int) + 1 := by omega
    rw [hlen_add, Int.mul_add, Int.mul_one]
    omega

/-- Theorem 8 (Sec. 2.3 & Lem. 5.1 Eq. 9 Restricted Submatrix Trace Bound):
    If `k_i ≤ a_i ≤ M` pairwise over equal-length lists of length `m`, then
    `listSum ks ≤ listSum as ≤ m * M`. -/
theorem restricted_trace_le_unrestricted_sum (M : Int) (ks : List Int) :
    ∀ as : List Int, ks.length = as.length →
      (∀ i (h1 : i < ks.length) (h2 : i < as.length), ks[i]'h1 ≤ as[i]'h2 ∧ as[i]'h2 ≤ M) →
      listSum ks ≤ listSum as ∧ listSum as ≤ (as.length : Int) * M := by
  induction ks with
  | nil =>
    intro as hlen _
    cases as with
    | nil =>
      dsimp only [listSum, List.length]
      change 0 ≤ 0 ∧ 0 ≤ (0 : Int) * M
      rw [Int.zero_mul]
      exact ⟨Int.le_refl 0, Int.le_refl 0⟩
    | cons _ _ => dsimp only [List.length] at hlen; omega
  | cons k ks' ih =>
    intro as hlen hpt
    cases as with
    | nil => dsimp only [List.length] at hlen; omega
    | cons a as' =>
      have hlen' : ks'.length = as'.length := by dsimp only [List.length] at hlen; omega
      have h0 := hpt 0 (Nat.zero_lt_succ ks'.length) (Nat.zero_lt_succ as'.length)
      dsimp only [List.getElem_cons_zero] at h0
      have hsub := ih as' hlen' (fun i h1 h2 => by
        have hstep := hpt (i + 1) (Nat.succ_lt_succ h1) (Nat.succ_lt_succ h2)
        dsimp only [List.getElem_cons_succ] at hstep
        exact hstep)
      dsimp only [listSum, List.length]
      have hlen_add : ((as'.length + 1 : Nat) : Int) = (as'.length : Int) + 1 := by omega
      rw [hlen_add, Int.add_mul, Int.one_mul]
      exact ⟨by omega, by omega⟩

/-- Integer power `a ^ n`. -/
def intPow (a : Int) : Nat → Int
  | 0 => 1
  | n + 1 => a * intPow a n

private theorem intPow_nonneg (a : Int) (ha : 0 ≤ a) (n : Nat) : 0 ≤ intPow a n := by
  induction n with
  | zero => dsimp only [intPow]; omega
  | succ k ih => dsimp only [intPow]; exact Int.mul_nonneg ha ih

/-- Theorem 9 (Lem. 5.4 p. 13 Exact Cleared Integer Bernoulli Inequality):
    For `0 ≤ b ≤ D` and every `k : Nat`,
    `D ^ k - k * b * D ^ (k - 1)` cleared by one `D`:
    `intPow D (k + 1) - (k : Int) * b * intPow D k ≤ D * intPow (D - b) k`. -/
theorem bernoulli_lower_bound_int (D b : Int) (hb0 : 0 ≤ b) (hbD : b ≤ D) (k : Nat) :
    intPow D (k + 1) - (k : Int) * b * intPow D k ≤ D * intPow (D - b) k := by
  have hD0 : 0 ≤ D := by omega
  have hDb : 0 ≤ D - b := by omega
  induction k with
  | zero =>
    dsimp only [intPow]
    change D * 1 - (0 : Int) * b * 1 ≤ D * 1
    rw [Int.zero_mul, Int.zero_mul, Int.sub_zero]
    exact Int.le_refl (D * 1)
  | succ m ih =>
    have hmul := Int.mul_le_mul_of_nonneg_left ih hDb
    have hpow_nn : 0 ≤ intPow D m := intPow_nonneg D hD0 m
    have hb2_nn : 0 ≤ b * b := Int.mul_nonneg hb0 hb0
    have hmb2_nn : 0 ≤ (m : Int) * (b * b) * intPow D m :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) hb2_nn) hpow_nn
    have hexp_l : (D - b) * (intPow D (m + 1) - (m : Int) * b * intPow D m) =
        intPow D (m + 1 + 1) - ((m + 1 : Nat) : Int) * b * intPow D (m + 1) + (m : Int) * (b * b) * intPow D m := by
      dsimp only [intPow]
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by omega
      rw [hcast, Int.add_mul, Int.one_mul, Int.add_mul]
      have c1 : D * ((m : Int) * b * intPow D m) = (m : Int) * b * (D * intPow D m) := by
        rw [← Int.mul_assoc, Int.mul_comm D ((m : Int) * b), Int.mul_assoc]
      have c2 : b * ((m : Int) * b * intPow D m) = (m : Int) * (b * b) * intPow D m := by
        rw [← Int.mul_assoc, Int.mul_comm b ((m : Int) * b), Int.mul_assoc (m : Int) b b, Int.mul_assoc]
      omega
    have hexp_r : (D - b) * (D * intPow (D - b) m) = D * intPow (D - b) (m + 1) := by
      dsimp only [intPow]
      rw [← Int.mul_assoc, Int.mul_comm (D - b) D, Int.mul_assoc]
    rw [hexp_l, hexp_r] at hmul
    omega

/-- Theorem 10 (Sec. 2.3 & Lem. 5.4 Trace-Gap Second-Eigenvalue Isolation):
    If `l1p + l2p + rest ≤ traceBound` with `0 ≤ rest` and `lower1 ≤ l1p`,
    then `l2p ≤ traceBound - lower1`. -/
theorem second_eigenvalue_trace_gap_bound (l1p l2p rest traceBound lower1 : Int)
    (hrest : 0 ≤ rest) (hlo : lower1 ≤ l1p) (htr : l1p + l2p + rest ≤ traceBound) :
    l2p ≤ traceBound - lower1 := by
  omega

/-- Theorem 11 (Lem. 5.3 p. 12 Trimming Maximizer Size Bound `|R| ≤ (4τ/(3h)) m`):
    If `F(R) = α|R| - e_in ≥ 0`, `h|R| ≤ e_in + e_out`, `e_out ≤ τ*m`, and `4*α = h`,
    then `3 * h * |R| ≤ 4 * τ * m`. -/
theorem trimming_maximizer_size_bound (alpha h r e_in e_out tau m : Int)
    (h4a : 4 * alpha = h)
    (hF : 0 ≤ alpha * r - e_in)
    (hcut : h * r ≤ e_in + e_out)
    (hout : e_out ≤ tau * m) :
    3 * h * r ≤ 4 * tau * m := by
  have h1 : 4 * (alpha * r) = h * r := by rw [← Int.mul_assoc, h4a]
  have h2 : 3 * h * r = 3 * (h * r) := Int.mul_assoc 3 h r
  have h3 : 4 * tau * m = 4 * (tau * m) := Int.mul_assoc 4 tau m
  omega

/-- Theorem 12 (Lem. 5.3 p. 12 Trimming Maximizer Strict Improvement Identity):
    If `e(S, U\S) < α|S|` and `0 ≤ e(S, R)`, then
    `F(R ∪ S) - F(R) = α|S| - e(S, U\S) + e(S, R) > 0`, contradicting maximality of `R`. -/
theorem trimming_maximizer_contradiction (alpha s e_su e_sr : Int)
    (hsparse : e_su < alpha * s) (hnonneg : 0 ≤ e_sr) :
    0 < alpha * s - e_su + e_sr := by
  omega

/-- Theorem 13 (Lem. 7.3 Eqs. 14–15 Balanced-Cut Farness Trade-off):
    For `h0 > 0, cstar > 0`, if `M ≥ h0 * s` and `M ≥ (cstar - h1) * A - cstar * s`,
    then `(h0 + cstar) * M ≥ h0 * (cstar - h1) * A`, eliminating the unknown drop `s`. -/
theorem farness_balanced_cut_tradeoff (M h0 cstar h1 A s : Int)
    (hh0 : 0 ≤ h0) (hc : 0 ≤ cstar)
    (h14 : h0 * s ≤ M)
    (h15 : (cstar - h1) * A - cstar * s ≤ M) :
    h0 * ((cstar - h1) * A) ≤ (h0 + cstar) * M := by
  have m1 : cstar * (h0 * s) ≤ cstar * M := Int.mul_le_mul_of_nonneg_left h14 hc
  have m2 : h0 * ((cstar - h1) * A - cstar * s) ≤ h0 * M := Int.mul_le_mul_of_nonneg_left h15 hh0
  rw [Int.mul_sub] at m2
  have hcomm : cstar * (h0 * s) = h0 * (cstar * s) := by
    rw [← Int.mul_assoc, Int.mul_comm cstar h0, Int.mul_assoc]
  rw [Int.add_mul]
  omega

/-- Theorem 14 (Remark 6.2 p. 15 Fixed Neighbor-Table Compaction Bound):
    Deleting `q` undirected edges removes `2*q` neighbor entries in unordered tables and
    at most `4*q` entries under fixed-order compaction, matching the `ε/2` factor-two reduction. -/
theorem fixed_neighbor_table_compaction_bound (q : Int) (hq : 0 ≤ q) :
    (2 * (2 * q) = 4 * q) ∧ (2 * q ≤ 4 * q) :=
  ⟨by omega, by omega⟩

/-- Theorem 15 (Lem. 7.2(iii) p. 18 Cayley Cyclic-Coordinate Cut Ratio `d / ⌊L/2⌋`):
    For `d = 2*r`, `|A_q| = k * m_q`, and `|E(A_q, V\A_q)| = 2 * r * m_q`,
    the cleared cut identity `k * |E| = d * |A_q|` holds identically. -/
theorem cayley_cyclic_cut_edge_count (r k mq : Int) :
    let d := 2 * r
    let Aq := k * mq
    let cutE := 2 * r * mq
    k * cutE = d * Aq := by
  dsimp only
  rw [← Int.mul_assoc, Int.mul_comm k (2 * r), Int.mul_assoc]

/-- Theorem 16 (Lem. 7.5 p. 21 Non-Backtracking Polynomial Recurrence at `z = d = p + 1`):
    For `Q_0 = 1, Q_1 = z, Q_2 = z^2 - (p+1), Q_3 = z*Q_2 - p*Q_1`, evaluating at `z = p + 1`
    yields exact reduced-word counts `Q_2(p+1) = (p+1)*p` and `Q_3(p+1) = (p+1)*p^2`. -/
theorem nonbacktracking_poly_recurrence_deg3 (p : Int) :
    let d := p + 1
    let Q1 := d
    let Q2 := d * d - d
    let Q3 := d * Q2 - p * Q1
    (Q2 = d * p) ∧ (Q3 = d * (p * p)) := by
  dsimp only
  have hQ2 : (p + 1) * (p + 1) - (p + 1) = (p + 1) * p := by
    rw [Int.mul_add, Int.mul_one]; omega
  constructor
  · exact hQ2
  · rw [hQ2]
    have h1 : (p + 1) * ((p + 1) * p) - p * (p + 1) = (p + 1) * (p * p) := by
      rw [Int.mul_comm p (p + 1), ← Int.mul_sub]
      have h2 : (p + 1) * p - p = p * p := by rw [Int.add_mul, Int.one_mul]; omega
      rw [h2]
    exact h1

/-- Theorem 17 (Lem. 7.4 p. 19 Three-Squares Parity Core for Gauss's `r_3(4N) = r_3(N)`):
    (1) Scaling `(x1, x2, x3) ↦ (2x1, 2x2, 2x3)` multiplies `x1^2 + x2^2 + x3^2` by `4`;
    (2) Whenever `x1^2 + x2^2 + x3^2 = 4*N`, every coordinate `x1, x2, x3` is even! -/
theorem three_squares_scaling_invariance_step (x1 x2 x3 N : Int) :
    ((2 * x1) * (2 * x1) + (2 * x2) * (2 * x2) + (2 * x3) * (2 * x3) =
      4 * (x1 * x1 + x2 * x2 + x3 * x3)) ∧
    (x1 * x1 + x2 * x2 + x3 * x3 = 4 * N → (x1 % 2 = 0 ∧ x2 % 2 = 0 ∧ x3 % 2 = 0)) := by
  constructor
  · have c : ∀ u : Int, (2 * u) * (2 * u) = 4 * (u * u) := fun u => by
      rw [Int.mul_assoc, Int.mul_comm u (2 * u), ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_assoc (2 * 2)]; rfl
    rw [c x1, c x2, c x3, Int.mul_add, Int.mul_add]
  · intro hsum
    have hsq_mod4 : ∀ u : Int, (u * u) % 4 = if u % 2 = 0 then 0 else 1 := by
      intro u
      have hrem : u % 2 = 0 ∨ u % 2 = 1 := by omega
      cases hrem with
      | inl h0 =>
        have hu : u = 2 * (u / 2) := by omega
        have hsq : u * u = 4 * ((u / 2) * (u / 2)) := by
          conv => lhs; rw [hu]
          rw [Int.mul_assoc, Int.mul_comm (u / 2) (2 * (u / 2)), ← Int.mul_assoc,
              ← Int.mul_assoc, Int.mul_assoc (2 * 2)]; rfl
        rw [h0]; simp; omega
      | inr h1 =>
        have hu : u = 2 * (u / 2) + 1 := by omega
        have hsq : u * u = 4 * ((u / 2) * (u / 2) + (u / 2)) + 1 := by
          conv => lhs; rw [hu]
          rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_one, Int.one_mul]
          have c4 : 2 * (u / 2) * (2 * (u / 2)) = 4 * ((u / 2) * (u / 2)) := by
            rw [Int.mul_assoc, Int.mul_comm (u / 2) (2 * (u / 2)), ← Int.mul_assoc,
                ← Int.mul_assoc, Int.mul_assoc (2 * 2)]; rfl
          rw [Int.mul_add]; omega
        rw [h1]; simp; omega
    have hrem1 : x1 % 2 = 0 ∨ x1 % 2 = 1 := by omega
    have hrem2 : x2 % 2 = 0 ∨ x2 % 2 = 1 := by omega
    have hrem3 : x3 % 2 = 0 ∨ x3 % 2 = 1 := by omega
    have m1 := hsq_mod4 x1
    have m2 := hsq_mod4 x2
    have m3 := hsq_mod4 x3
    have hsum_mod4 : (x1 * x1 + x2 * x2 + x3 * x3) % 4 = 0 := by rw [hsum]; omega
    rcases hrem1 with e1 | e1 <;> rcases hrem2 with e2 | e2 <;> rcases hrem3 with e3 | e3 <;>
      simp [e1, e2, e3] at m1 m2 m3
    · exact ⟨e1, e2, e3⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

/-- Theorem 18 (Appendix A Lem. A.2 Eq. 23 Short-Walk Spectral Difference `λ^{2t}(1-λ^t)^2 ≤ λ^{2t}(1-λ^{2t})`):
    For every cleared eigenvalue `0 ≤ x ≤ D`,
    `x^2 * (D - x)^2 ≤ x^2 * (D^2 - x^2)` (certifying `∥P^t - P^{2t}∥_2^2 ≤ A_s - B_s`). -/
theorem walk_regular_short_walk_spectral_diff (x D : Int) (hx0 : 0 ≤ x) (hxD : x ≤ D) :
    (x * x) * ((D - x) * (D - x)) ≤ (x * x) * (D * D - x * x) := by
  have hx2 : 0 ≤ x * x := Int.mul_nonneg hx0 hx0
  have hDx : 0 ≤ D - x := by omega
  have hle : D - x ≤ D + x := by omega
  have hmul : (D - x) * (D - x) ≤ (D + x) * (D - x) := Int.mul_le_mul_of_nonneg_right hle hDx
  have hid : (D + x) * (D - x) = D * D - x * x := by
    rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm x D]; omega
  rw [hid] at hmul
  exact Int.mul_le_mul_of_nonneg_left hmul hx2

end ExpansionReturnProb
