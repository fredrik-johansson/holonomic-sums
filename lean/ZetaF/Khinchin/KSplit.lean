/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Algorithms K1 and K2 in the form of Theorem 3.2

Both summands of (K1) and (K2) are analytic at infinity and vanish to second order:
`μ_k = k^{-2} ∑_n b_n k^{-n}` with `b_n = (-1)^n (2^{n+2} - 2)/((n+2) log 2)` (from
`μ_k log 2 = 2 log(1 + 1/k) - log(1 + 2/k)`), and
`F(k) = -log(1 - 1/k) log(1 + 1/k) = k^{-2} ∑_n c_n k^{-n}` with
`c_n = ∑_{i ≤ n} (-1)^{n-i}/((i+1)(n-i+1))` (a Cauchy product). Hence `ζ_μ(s) = ζ_G(s+2)` with
`G(k) = k² μ_k = ∑ b_n k^{-n}`, and the splitting of Theorem 3.2 (`splitRHS`) applies at the regular
point `s + 2`, near `s = 0`:

* **(K1)** `log K = ∑_{1 ≤ k < k₀} μ_k log k - (d/ds) splitRHS(b; k₀, u₀)(2)`;
* **(K2)** `log K log 2 = ∑_{2 ≤ k < k₀} F(k) + splitRHS(c; k₀, u₀)(2)`,

for every `k₀ ≥ 3` and `u₀ > 0`.
-/
import ZetaF.Khinchin.K1
import ZetaF.Continuation.Regular

open Filter Topology Real LSeries
open scoped Nat

namespace ZetaF.KSplit

open ZetaF

/-! ### Generalities: head and tail, and the shift `s ↦ s + 2` -/

lemma LSeries_eq_head_add_zetaTail {F : ℕ → ℂ} {s : ℂ} {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hsumF : LSeriesSummable F s) :
    LSeries F s = ∑ k ∈ Finset.Ico 1 k₀, F k * (k : ℂ) ^ (-s) + zetaTail F k₀ s := by
  have hsum : LSeriesSummable (tail k₀ F) s := by
    refine (LSeriesSummable_congr' s ?_).1 hsumF
    filter_upwards [eventually_ge_atTop k₀] with n hn
    simp [tail, hn]
  unfold zetaTail LSeries
  rw [← hsumF.sum_add_tsum_nat_add k₀, ← hsum.sum_add_tsum_nat_add k₀]
  have h1 : ∑ i ∈ Finset.range k₀, term (tail k₀ F) s i = 0 := Finset.sum_eq_zero fun i hi => by
    simp only [Finset.mem_range] at hi; simp [term, tail, show ¬ k₀ ≤ i by omega]
  have h2 : ∀ i, term (tail k₀ F) s (i + k₀) = term F s (i + k₀) := fun i => by
    simp [term, tail]
  have h3 : ∑ i ∈ Finset.range k₀, term F s i = ∑ k ∈ Finset.Ico 1 k₀, F k * (k : ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hk₀]
    simp only [Finset.Ico_self, Nat.Ico_zero_eq_range, Finset.range_one, Finset.sum_singleton,
      term_zero, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Ico] at hk
    rw [term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
  rw [h1, zero_add, h3]
  simp only [h2]

lemma term_shift_two {F G : ℕ → ℂ} (hG : ∀ k, k ≠ 0 → G k = (k : ℂ) ^ 2 * F k) (s : ℂ) (n : ℕ) :
    term F s n = term G (s + 2) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [term_of_ne_zero hn, term_of_ne_zero hn, hG n hn, Complex.cpow_add _ _ hn',
      show (n : ℂ) ^ (2 : ℂ) = (n : ℂ) ^ (2 : ℕ) by norm_cast]
    field_simp

lemma LSeries_shift_two {F G : ℕ → ℂ} (hG : ∀ k, k ≠ 0 → G k = (k : ℂ) ^ 2 * F k) (s : ℂ) :
    LSeries F s = LSeries G (s + 2) := by
  unfold LSeries; simp_rw [term_shift_two hG s]

lemma zetaTail_shift_two {F G : ℕ → ℂ} (hG : ∀ k, k ≠ 0 → G k = (k : ℂ) ^ 2 * F k) (k₀ : ℕ)
    (s : ℂ) : zetaTail F k₀ s = zetaTail G k₀ (s + 2) := by
  unfold zetaTail
  refine LSeries_shift_two (fun k hk => ?_) s
  simp only [tail]; split_ifs <;> simp [hG k hk]

/-! ### (K1) -/

/-- `b_n = (-1)^n (2^{n+2} - 2)/((n+2) log 2)`, the expansion of `k² μ_k` in `1/k`. -/
noncomputable def bK1 (n : ℕ) : ℝ := (-1) ^ n * (2 ^ (n + 2) - 2) / ((n + 2) * Real.log 2)

lemma log_series {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (-x) ^ (n + 1) / (n + 1)) (-Real.log (1 + x)) := by
  have := Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by rwa [abs_neg])
  rwa [sub_neg_eq_add] at this

/-- `k² μ_k = ∑_n b_n k^{-n}` for `k ≥ 3`. -/
lemma hasSum_gkMu (k : ℕ) (hk : 3 ≤ k) :
    HasSum (fun n : ℕ => bK1 n * ((k : ℝ)⁻¹) ^ n) ((k : ℝ) ^ 2 * gkMu k) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set x : ℝ := (k : ℝ)⁻¹
  have hx0 : 0 < x := inv_pos.2 hk0
  have hx3 : x ≤ 1 / 3 := by rw [one_div]; exact inv_anti₀ (by norm_num) hk'
  have h1 := log_series (x := x) (by rw [abs_of_pos hx0]; linarith)
  have h2 := log_series (x := 2 * x) (by rw [abs_of_pos (by positivity)]; linarith)
  -- `μ_k log 2 = 2 log(1+x) - log(1+2x)`
  have hlog : Real.log (1 + 1 / ((k : ℝ) * (k + 2))) = 2 * Real.log (1 + x) - Real.log (1 + 2 * x) := by
    have e : 1 + 1 / ((k : ℝ) * (k + 2)) = (1 + x) ^ 2 / (1 + 2 * x) := by
      simp only [x]; field_simp; ring
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have hS := (h2.sub (h1.mul_left 2))
  rw [show -Real.log (1 + 2 * x) - 2 * -Real.log (1 + x) = 2 * Real.log (1 + x) - Real.log (1 + 2 * x)
    by ring, ← hlog] at hS
  have hS1 := (hasSum_nat_add_iff' 1).2 hS
  simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, zero_add, pow_one,
    div_one] at hS1
  rw [show (-(2 * x)) - 2 * (-x) = 0 by ring, sub_zero] at hS1
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS2 := (hS1.div_const (Real.log 2)).mul_left ((k : ℝ) ^ 2)
  have hkx : (k : ℝ) ^ 2 * x ^ 2 = 1 := by simp only [x]; field_simp
  convert hS2 using 1
  · ext n
    unfold bK1
    have hn2 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [hn2, show n + 1 + 1 = n + 2 by ring]
    have e1 : (-(2 * x)) ^ (n + 2) = (-1) ^ n * 2 ^ (n + 2) * x ^ (n + 2) := by
      rw [neg_pow, mul_pow, show (-1 : ℝ) ^ (n + 2) = (-1) ^ n by rw [pow_add]; norm_num]; ring
    have e2 : (-x) ^ (n + 2) = (-1) ^ n * x ^ (n + 2) := by
      rw [neg_pow, show (-1 : ℝ) ^ (n + 2) = (-1) ^ n by rw [pow_add]; norm_num]
    rw [e1, e2, pow_add x n 2]
    have h' : (k : ℝ) ^ 2 * (((-1) ^ n * 2 ^ (n + 2) * (x ^ n * x ^ 2) / ((n : ℝ) + 2) -
        2 * ((-1) ^ n * (x ^ n * x ^ 2) / ((n : ℝ) + 2))) / Real.log 2) =
        ((k : ℝ) ^ 2 * x ^ 2) * ((-1) ^ n * (2 ^ (n + 2) - 2) / (((n : ℝ) + 2) * Real.log 2) * x ^ n) := by
      have hn2' : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
    rw [h', hkx, one_mul]
  · unfold gkMu; ring

lemma geomBounded_bK1 : GeomBounded (fun n => (bK1 n : ℂ)) 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 / Real.log 2, fun n => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, bK1]
  have h2le : (2 : ℝ) ≤ 2 ^ (n + 2) := le_self_pow₀ (by norm_num) (by omega)
  have hden : 0 < ((n : ℝ) + 2) * Real.log 2 := by positivity
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hden,
    abs_of_nonneg (by linarith), div_le_iff₀ hden]
  have e : 4 / Real.log 2 * 2 ^ n * (((n : ℝ) + 2) * Real.log 2) = 4 * 2 ^ n * ((n : ℝ) + 2) := by
    field_simp
  rw [e, pow_add]
  have h0 : (0 : ℝ) ≤ 2 ^ n := by positivity
  nlinarith [mul_nonneg h0 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)] : (0 : ℝ) ≤ (n : ℝ) + 1)]

/-- `G(k) = k² μ_k`, as a complex sequence. -/
noncomputable def GK1 (k : ℕ) : ℂ := ((k : ℝ) ^ 2 * gkMu k : ℝ)

lemma GK1_eq_evalInv {k : ℕ} (hk : 3 ≤ k) : GK1 k = evalInv (fun n => (bK1 n : ℂ)) k := by
  unfold GK1 evalInv
  rw [← (hasSum_gkMu k hk).tsum_eq, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast; rfl

lemma GK1_shift (k : ℕ) (hk : k ≠ 0) : GK1 k = (k : ℂ) ^ 2 * gkMuC k := by
  unfold GK1 gkMuC; push_cast; ring

lemma abscissa_gkMuC_le : abscissaOfAbsConv gkMuC ≤ ((-2 : ℝ) + 1 : ℝ) := by
  refine abscissaOfAbsConv_le_of_le_const_mul_rpow ⟨1 / Real.log 2, fun n hn => ?_⟩
  rw [gkMuC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact gkMu_le n hn
  · rcases n with _ | n
    · exact absurd rfl hn
    · exact gkMu_nonneg n

/-- `Z(s) = ∑_{1 ≤ k < k₀} μ_k k^{-s} + splitRHS(b; k₀, u₀)(s+2)` for `Re s > -1`. -/
theorem khinchinZ_eq_split {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) {s : ℂ}
    (hs : -1 < s.re) :
    khinchinZ s = ∑ k ∈ Finset.Ico 1 k₀, gkMuC k * (k : ℂ) ^ (-s) +
      splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀ (s + 2) := by
  have hsum : LSeriesSummable gkMuC s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    exact lt_of_le_of_lt abscissa_gkMuC_le (by exact_mod_cast (by norm_num; linarith : (-2 : ℝ) + 1 < s.re))
  rw [khinchinZ_eq_LSeries, LSeries_eq_head_add_zetaTail (k₀ := k₀) (by omega) hsum,
    zetaTail_shift_two GK1_shift k₀ s,
    zetaTail_eq_splitRHS (k₀ := k₀) geomBounded_bK1 (by norm_num) (by omega)
      (by exact_mod_cast (by omega : 2 < k₀)) (fun k hk => GK1_eq_evalInv (by omega)) hu₀
      (by simp; linarith)]

/-- **Algorithm K1 in the form of Theorem 3.2**: for `k₀ ≥ 3`, `u₀ > 0`,
`log K = ∑_{1 ≤ k < k₀} μ_k log k - (d/ds) splitRHS(b; k₀, u₀)(2)`. -/
theorem logK_split {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    (logK : ℂ) = ∑ k ∈ Finset.Ico 1 k₀, gkMuC k * Complex.log k -
      deriv (splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀) 2 := by
  set H : ℂ → ℂ := fun s => ∑ k ∈ Finset.Ico 1 k₀, gkMuC k * (k : ℂ) ^ (-s) +
    splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀ (s + 2)
  have hev : khinchinZ =ᶠ[𝓝 0] H := by
    have hopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp)] with s hs
    exact khinchinZ_eq_split hk₀ hu₀ hs
  have hd2 : DifferentiableAt ℂ (splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀) 2 := by
    have hD := differentiableOn_splitRHS geomBounded_bK1 (by norm_num)
      (by exact_mod_cast (by omega : 2 < k₀)) hu₀
    refine hD.differentiableAt (isOpen_notPoles.mem_nhds fun n h => ?_)
    have := congrArg Complex.re h
    simp at this
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hderiv : HasDerivAt H (∑ k ∈ Finset.Ico 1 k₀, gkMuC k * (-Complex.log k) +
      deriv (splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀) 2) 0 := by
    refine HasDerivAt.add (HasDerivAt.fun_sum fun k hk => ?_) ?_
    · have hk0 : (k : ℂ) ≠ 0 := by
        simp only [Finset.mem_Ico] at hk; exact_mod_cast (by omega : k ≠ 0)
      have h := ((hasDerivAt_neg (0 : ℂ)).const_cpow (c := (k : ℂ)) (Or.inl hk0)).const_mul
        (gkMuC k)
      convert h using 1
      simp
    · have h2 : HasDerivAt (splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀)
          (deriv (splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀) 2) ((0 : ℂ) + 2) := by
        rw [zero_add]; exact hd2.hasDerivAt
      exact h2.comp_add_const 0 2
  have e := hasDerivAt_khinchinZ_zero.unique (hderiv.congr_of_eventuallyEq hev)
  have e2 : (logK : ℂ) = -(∑ k ∈ Finset.Ico 1 k₀, gkMuC k * (-Complex.log k) +
      deriv (splitRHS (fun n => (bK1 n : ℂ)) k₀ u₀) 2) := by rw [← e, neg_neg]
  rw [e2]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-! ### (K2) -/

/-- `c_n = ∑_{i ≤ n} (-1)^{n-i}/((i+1)(n-i+1))`: the expansion of `k² F(k)` in `1/k`. -/
noncomputable def cK2 (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (-1) ^ (n - i) / (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1))

lemma abs_cK2_le (n : ℕ) : |cK2 n| ≤ n + 1 := by
  unfold cK2
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), |(-1 : ℝ) ^ (n - i) / (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1))|
      ≤ ∑ i ∈ Finset.range (n + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_pos (by positivity : (0 : ℝ) < ((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1))]
        rw [div_le_one (by positivity)]
        nlinarith [(i.cast_nonneg : (0 : ℝ) ≤ i), ((n - i : ℕ).cast_nonneg : (0 : ℝ) ≤ (n - i : ℕ))]
    _ = n + 1 := by simp

lemma geomBounded_cK2 : GeomBounded (fun n => (cK2 n : ℂ)) 2 := by
  refine ⟨1, fun n => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
  refine (abs_cK2_le n).trans ?_
  have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  exact_mod_cast this

/-- `-log(1-x) log(1+x) = x² ∑_n c_n x^n` for `|x| < 1`. -/
lemma hasSum_F {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => x ^ 2 * (cK2 n * x ^ n)) (-(Real.log (1 - x) * Real.log (1 + x))) := by
  set P : ℕ → ℝ := fun i => x ^ (i + 1) / (i + 1)
  set Q : ℕ → ℝ := fun j => -((-x) ^ (j + 1) / (j + 1))
  have hP : HasSum P (-Real.log (1 - x)) := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have hQ : HasSum Q (Real.log (1 + x)) := by
    have := (log_series hx).neg; rwa [neg_neg] at this
  have hgeom : Summable fun i : ℕ => |x| ^ (i + 1) :=
    (summable_geometric_of_lt_one (abs_nonneg x) hx).comp_injective (add_left_injective 1)
  have hPn : Summable fun i => ‖P i‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hgeom
    simp only [P, Real.norm_eq_abs, abs_div, abs_pow]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
    exact div_le_self (by positivity) (by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
  have hQn : Summable fun j => ‖Q j‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hgeom
    simp only [Q, Real.norm_eq_abs, abs_neg, abs_div, abs_pow]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
    exact div_le_self (by positivity) (by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hPn hQn
  have hsumm := summable_sum_mul_range_of_summable_norm' hPn hP.summable hQn hQ.summable
  rw [hP.tsum_eq, hQ.tsum_eq] at hprod
  have hterm : ∀ n, ∑ k ∈ Finset.range (n + 1), P k * Q (n - k) = x ^ 2 * (cK2 n * x ^ n) := by
    intro n
    unfold cK2
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    simp only [P, Q]
    have e : (-x) ^ (n - i + 1) = (-1) ^ (n - i + 1) * x ^ (n - i + 1) := by rw [neg_pow]
    have hxx : x ^ (i + 1) * x ^ (n - i + 1) = x ^ 2 * x ^ n := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [e, show x ^ 2 * ((-1) ^ (n - i) / (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1)) * x ^ n) =
      (-1) ^ (n - i) / (((i : ℝ) + 1) * (((n - i : ℕ) : ℝ) + 1)) * (x ^ 2 * x ^ n) by ring, ← hxx,
      pow_succ (-1 : ℝ) (n - i)]
    have h1 : (i : ℝ) + 1 ≠ 0 := by positivity
    have h2 : ((n - i : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [show -(Real.log (1 - x) * Real.log (1 + x)) = -Real.log (1 - x) * Real.log (1 + x) by ring,
    hprod]
  simp_rw [← hterm]
  exact hsumm.hasSum

/-- `F(k) = -log(1 - 1/k) log(1 + 1/k)`, as a complex sequence (`F(0) = F(1) = 0` in Lean). -/
noncomputable def FK2 (k : ℕ) : ℂ := (-(Real.log (1 - 1 / k) * Real.log (1 + 1 / k)) : ℝ)

/-- `G(k) = k² F(k)`. -/
noncomputable def GK2 (k : ℕ) : ℂ := ((k : ℝ) ^ 2 * -(Real.log (1 - 1 / k) * Real.log (1 + 1 / k)) : ℝ)

lemma GK2_shift (k : ℕ) (_hk : k ≠ 0) : GK2 k = (k : ℂ) ^ 2 * FK2 k := by
  unfold GK2 FK2; push_cast; ring

lemma GK2_eq_evalInv {k : ℕ} (hk : 2 ≤ k) : GK2 k = evalInv (fun n => (cK2 n : ℂ)) k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : |(1 / (k : ℝ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by linarith)]; linarith
  have h := (hasSum_F hx).mul_left ((k : ℝ) ^ 2)
  unfold GK2 evalInv
  rw [← h.tsum_eq, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, ← mul_pow, mul_one_div_cancel hk0, one_pow, one_mul]
  push_cast
  simp [one_div]

lemma FK2_one : FK2 1 = 0 := by simp [FK2]

/-- **Algorithm K2 in the form of Theorem 3.2**: for `k₀ ≥ 3`, `u₀ > 0`,
`log K log 2 = ∑_{2 ≤ k < k₀} F(k) + splitRHS(c; k₀, u₀)(2)`. -/
theorem logK_mul_log_two_split {k₀ : ℕ} (hk₀ : 3 ≤ k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ((logK * Real.log 2 : ℝ) : ℂ) = ∑ k ∈ Finset.Ico 2 k₀, FK2 k +
      splitRHS (fun n => (cK2 n : ℂ)) k₀ u₀ 2 := by
  -- `log K log 2 = ∑_{k ≥ 1} F(k) = LSeries F 0`
  have hF : HasSum (fun k : ℕ => FK2 (k + 2)) ((logK * Real.log 2 : ℝ) : ℂ) := by
    rw [logK_mul_log_two]
    have := (hasSum_khF).summable.hasSum
    rw [← Complex.hasSum_ofReal] at this
    convert this using 1
    · ext k; unfold FK2 khF; push_cast; ring_nf
    · rw [← logK_mul_log_two, hasSum_khF.tsum_eq]
  have hterm : ∀ n, term FK2 0 (n + 2) = FK2 (n + 2) := fun n => by
    rw [term_of_ne_zero (by omega), Complex.cpow_zero, div_one]
  have hsumF : LSeriesSummable FK2 0 := by
    unfold LSeriesSummable
    rw [← summable_nat_add_iff 2]
    simp_rw [hterm]; exact hF.summable
  have hL : LSeries FK2 0 = ((logK * Real.log 2 : ℝ) : ℂ) := by
    unfold LSeries
    rw [← hsumF.sum_add_tsum_nat_add 2]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, term_zero, zero_add]
    rw [term_of_ne_zero one_ne_zero, FK2_one, zero_div, zero_add]
    simp_rw [hterm]; exact hF.tsum_eq
  rw [← hL, LSeries_eq_head_add_zetaTail (k₀ := k₀) (by omega) hsumF, zetaTail_shift_two GK2_shift k₀ 0,
    zero_add, zetaTail_eq_splitRHS (k₀ := k₀) geomBounded_cK2 (by norm_num) (by omega)
      (by exact_mod_cast (by omega : 2 < k₀)) (fun k hk => GK2_eq_evalInv (by omega)) hu₀
      (by norm_num)]
  congr 1
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 1 ≤ 2) (by omega : 2 ≤ k₀)]
  simp [FK2_one]

end ZetaF.KSplit
