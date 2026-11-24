/-
# The series for the regularized lower incomplete gamma function (Appendix A.5)

For every `a ∈ ℂ` and `y > 0`,
`P(a, y) = 1 - Q(a, y) = y^a e^{-y} ∑_{i ≥ 0} y^i / Γ(a + i + 1)`,
which is the paper's `y^a e^{-y}/Γ(a) ∑ y^i/(a)_{i+1}` written so that it also covers
`a ∈ ℤ_{≤ 0}` (where `Q = 0`, `P = 1`).  The terms satisfy `t_{i+1} (a+i+1) = y t_i`, so once
`Re a + i + 1 ≥ 2y` they decrease at least geometrically with ratio `1/2`, and the tail from such an
`N` is at most `2|t_N|` (this gives the `O(p)` terms of Appendix A.5).
-/
import ZetaF.IncompleteGamma
import ZetaF.GammaUniform

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace ZetaF

/-- The lower incomplete gamma function `γ(b, x) = ∫₀^x t^{b-1} e^{-t} dt`. -/
noncomputable def lowerGamma (b : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioc 0 x, (t : ℂ) ^ (b - 1) * (Real.exp (-t) : ℂ)

lemma integrableOn_Ioi_zero_cpow_mul_exp {b : ℂ} (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (b - 1) * (Real.exp (-t) : ℂ)) (Ioi 0) := by
  refine (Complex.GammaIntegral_convergent hb).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only; ring

/-- `Γ(b) = γ(b, x) + Γ(b, x)` for `Re b > 0`. -/
lemma Gamma_eq_lower_add_upper {b : ℂ} (hb : 0 < b.re) {x : ℝ} (hx : 0 < x) :
    Gamma b = lowerGamma b x + upperGamma b x := by
  rw [Complex.Gamma_eq_integral hb, Complex.GammaIntegral, lowerGamma, upperGamma,
    ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((integrableOn_Ioi_zero_cpow_mul_exp hb).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_Ioi_zero_cpow_mul_exp hb).mono_set (Ioi_subset_Ioi hx.le)),
    Ioc_union_Ioi_eq_Ioi hx.le]
  congr 1; funext t; ring

/-- `|γ(b, x)| ≤ x^{Re b}/Re b`. -/
lemma norm_lowerGamma_le {b : ℂ} (hb : 0 < b.re) {x : ℝ} (hx : 0 < x) :
    ‖lowerGamma b x‖ ≤ x ^ b.re / b.re := by
  have hr : -1 < b.re - 1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ (b.re - 1)) (Ioc 0 x) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).1
      (intervalIntegral.intervalIntegrable_rpow' hr)
  calc ‖lowerGamma b x‖ ≤ ∫ t in Ioc 0 x, ‖(t : ℂ) ^ (b - 1) * (Real.exp (-t) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc 0 x, t ^ (b.re - 1) := by
        refine setIntegral_mono_on
          ((integrableOn_Ioi_zero_cpow_mul_exp hb).mono_set Ioc_subset_Ioi_self).norm hint
          measurableSet_Ioc fun t ht => ?_
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le]
        simp only [sub_re, one_re]
        refine mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _) ?_
        rw [Real.exp_le_one_iff, neg_nonpos]; exact ht.1.le
    _ = x ^ b.re / b.re := by
        rw [← intervalIntegral.integral_of_le hx.le, integral_rpow (Or.inl hr),
          Real.zero_rpow (by linarith), sub_zero, sub_add_cancel]

/-- The terms `t_i = y^{a+i} e^{-y}/Γ(a+i+1)` of the series for `P(a, y)`. -/
noncomputable def gammaPTerm (a : ℂ) (y : ℝ) (i : ℕ) : ℂ :=
  (y : ℂ) ^ (a + i) * (Real.exp (-y) : ℂ) * (Gamma (a + i + 1))⁻¹

lemma gammaQ_add_nat (a : ℂ) {y : ℝ} (hy : 0 < y) (N : ℕ) :
    gammaQ (a + N) y = gammaQ a y + ∑ i ∈ Finset.range N, gammaPTerm a y i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih, Nat.cast_succ, ← add_assoc,
      gammaQ_add_one _ hy, gammaPTerm]

lemma cpow_ofReal_norm {y : ℝ} (hy : 0 < y) (w : ℂ) : ‖(y : ℂ) ^ w‖ = y ^ w.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hy w

/-- `‖1/Γ(w + m)‖ ≤ gammaRatio(w) / Γ(Re w + m)` for `Re w > 0`. -/
lemma norm_inv_Gamma_add_nat_le {w : ℂ} (hw : 0 < w.re) (m : ℕ) :
    ‖(Gamma (w + m))⁻¹‖ ≤ gammaRatio w / Real.Gamma (w.re + m) := by
  have h := gammaRatio_add_nat_le hw m
  have hG : 0 < Real.Gamma (w.re + m) := Real.Gamma_pos_of_pos (by positivity)
  rw [le_div_iff₀ hG, mul_comm]
  unfold gammaRatio at h ⊢
  simpa using h

/-- The terms of the series are eventually bounded by a summable sequence. -/
lemma summable_gammaPTerm (a : ℂ) {y : ℝ} (hy : 0 < y) : Summable (gammaPTerm a y) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (-a.re)
  set w := a + N₀ + 1 with hw
  have hw0 : 0 < w.re := by simp [hw]; linarith
  refine (summable_nat_add_iff N₀).1 ?_
  have hs := (summable_pow_div_Gamma_add (y := w.re) (q := y) hw0 hy.le).mul_left
    (y ^ (a.re + N₀) * Real.exp (-y) * gammaRatio w)
  refine Summable.of_norm_bounded hs fun i => ?_
  rw [gammaPTerm, norm_mul, norm_mul, cpow_ofReal_norm hy, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : a + ((i + N₀ : ℕ) : ℂ) + 1 = w + i := by rw [hw]; push_cast; ring
  rw [h1]
  have h2 := norm_inv_Gamma_add_nat_le hw0 i
  have h3 : (a + ((i + N₀ : ℕ) : ℂ)).re = a.re + N₀ + i := by simp; ring
  rw [h3, Real.rpow_add hy, Real.rpow_natCast]
  have hp : 0 ≤ y ^ (a.re + N₀) * y ^ i * Real.exp (-y) := by positivity
  calc y ^ (a.re + N₀) * y ^ i * Real.exp (-y) * ‖(Gamma (w + i))⁻¹‖
      ≤ y ^ (a.re + N₀) * y ^ i * Real.exp (-y) * (gammaRatio w / Real.Gamma (w.re + i)) :=
        mul_le_mul_of_nonneg_left h2 hp
    _ = _ := by ring

/-- `Q(b, y) → 1` along `b = a + N`, `N → ∞`. -/
lemma tendsto_gammaQ_add_nat (a : ℂ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun N : ℕ => gammaQ (a + N) y) atTop (𝓝 1) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (-a.re)
  set w := a + N₀ + 1 with hw
  have hw0 : 0 < w.re := by simp [hw]; linarith
  -- `1 - Q(w + m, y) = γ(w+m, y)/Γ(w+m)`, bounded by `C y^{Re w + m}/Γ(Re w + m + 1)`
  have hbound : ∀ m : ℕ, ‖1 - gammaQ (w + m) y‖ ≤
      gammaRatio w * (y ^ w.re * (y ^ m / Real.Gamma (w.re + 1 + m))) := by
    intro m
    have hwm : 0 < (w + m).re := by simp; positivity
    have hG := Gamma_eq_lower_add_upper hwm hy
    have hG0 : Gamma (w + m) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hwm
    have : 1 - gammaQ (w + m) y = lowerGamma (w + m) y * (Gamma (w + m))⁻¹ := by
      rw [gammaQ, ← mul_inv_cancel₀ hG0, hG]; ring
    rw [this, norm_mul]
    have hl := norm_lowerGamma_le hwm hy
    have hi := norm_inv_Gamma_add_nat_le hw0 m
    have hre : (w + m).re = w.re + m := by simp
    rw [hre] at hl
    have hΓ : Real.Gamma (w.re + 1 + m) = (w.re + m) * Real.Gamma (w.re + m) := by
      rw [show w.re + 1 + m = (w.re + m) + 1 by ring, Real.Gamma_add_one (ne_of_gt (by positivity : (0 : ℝ) < w.re + m))]
    have hpos : 0 < Real.Gamma (w.re + m) := Real.Gamma_pos_of_pos (by positivity)
    have hgr : 0 ≤ gammaRatio w := gammaRatio_nonneg hw0
    calc ‖lowerGamma (w + m) y‖ * ‖(Gamma (w + m))⁻¹‖
        ≤ y ^ (w.re + m) / (w.re + m) * (gammaRatio w / Real.Gamma (w.re + m)) :=
          mul_le_mul hl hi (norm_nonneg _) (by positivity)
      _ = gammaRatio w * (y ^ w.re * (y ^ m / Real.Gamma (w.re + 1 + m))) := by
          rw [hΓ, Real.rpow_add hy, Real.rpow_natCast]
          field_simp
  have hlim : Tendsto (fun m : ℕ => gammaRatio w * (y ^ w.re * (y ^ m /
      Real.Gamma (w.re + 1 + m)))) atTop (𝓝 0) := by
    have := (summable_pow_div_Gamma_add (y := w.re + 1) (q := y) (by linarith)
      hy.le).tendsto_atTop_zero
    simpa using (this.const_mul (y ^ w.re)).const_mul (gammaRatio w)
  have hm : Tendsto (fun m : ℕ => gammaQ (w + m) y) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hlim
    rw [norm_sub_rev]; exact hbound m
  have := hm.comp (tendsto_sub_atTop_nat (N₀ + 1))
  refine (tendsto_congr' ?_).1 this
  filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
  simp only [Function.comp_apply, hw]
  congr 1
  push_cast [Nat.cast_sub hN]
  ring

/-- **Appendix A.5**: `P(a, y) = 1 - Q(a, y) = ∑_{i ≥ 0} y^{a+i} e^{-y}/Γ(a+i+1)` for every
`a ∈ ℂ` and `y > 0`. -/
theorem hasSum_gammaPTerm (a : ℂ) {y : ℝ} (hy : 0 < y) :
    HasSum (gammaPTerm a y) (1 - gammaQ a y) := by
  refine (summable_gammaPTerm a hy).hasSum_iff_tendsto_nat.2 ?_
  have := (tendsto_gammaQ_add_nat a hy).sub_const (gammaQ a y)
  refine (tendsto_congr fun N => ?_).1 this
  rw [gammaQ_add_nat a hy N]; ring

/-- At `a ∈ ℤ_{≤0}`: `Q(a, y) = 0` and hence `P(a, y) = 1`. -/
lemma gammaQ_neg_nat (m : ℕ) (y : ℝ) : gammaQ (-(m : ℂ)) y = 0 := by
  simp [gammaQ, Complex.Gamma_neg_nat_eq_zero]

/-- The ratio of consecutive terms: `t_{i+1} (a+i+1) = y t_i`. -/
lemma gammaPTerm_succ (a : ℂ) {y : ℝ} (hy : 0 < y) (i : ℕ) :
    gammaPTerm a y (i + 1) * (a + i + 1) = y * gammaPTerm a y i := by
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  unfold gammaPTerm
  have h1 : a + ((i + 1 : ℕ) : ℂ) = (a + i) + 1 := by push_cast; ring
  have h2 := mul_inv_Gamma_add_one (a + i + 1)
  rw [h1, Complex.cpow_add _ _ hy', Complex.cpow_one, show a + ↑i + 1 + 1 = (a + i + 1) + 1 by ring]
  rw [← h2]
  ring

/-- **Truncation**: if `Re a + N + 1 ≥ 2y` (and `> 0`), the tail of the series from `N` is at most
`2 |t_N|`. -/
theorem norm_tail_gammaPTerm_le (a : ℂ) {y : ℝ} (hy : 0 < y) {N : ℕ}
    (hN : 2 * y ≤ a.re + N + 1) :
    ‖∑' i : ℕ, gammaPTerm a y (i + N)‖ ≤ 2 * ‖gammaPTerm a y N‖ := by
  have hstep : ∀ i : ℕ, ‖gammaPTerm a y (i + N + 1)‖ ≤ ‖gammaPTerm a y (i + N)‖ / 2 := by
    intro i
    have h := gammaPTerm_succ a hy (i + N)
    have hre : 2 * y ≤ ‖a + ((i + N : ℕ) : ℂ) + 1‖ := by
      refine hN.trans ((?_ : a.re + N + 1 ≤ (a + ((i + N : ℕ) : ℂ) + 1).re).trans
        (Complex.re_le_norm _))
      simp
    have hn := congrArg norm h
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hy.le] at hn
    have hpos : 0 < ‖a + ((i + N : ℕ) : ℂ) + 1‖ := by linarith
    have : ‖gammaPTerm a y (i + N + 1)‖ = y * ‖gammaPTerm a y (i + N)‖ /
        ‖a + ((i + N : ℕ) : ℂ) + 1‖ := by
      rw [eq_div_iff hpos.ne', hn]
    rw [this, div_le_div_iff₀ hpos two_pos]
    nlinarith [norm_nonneg (gammaPTerm a y (i + N))]
  have hgeom : ∀ i : ℕ, ‖gammaPTerm a y (i + N)‖ ≤ ‖gammaPTerm a y N‖ * (1 / 2) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show i + 1 + N = i + N + 1 by ring, pow_succ]
      calc ‖gammaPTerm a y (i + N + 1)‖ ≤ ‖gammaPTerm a y (i + N)‖ / 2 := hstep i
        _ ≤ ‖gammaPTerm a y N‖ * (1 / 2) ^ i / 2 := by gcongr
        _ = _ := by ring
  have hs := (summable_geometric_two).mul_left ‖gammaPTerm a y N‖
  calc ‖∑' i : ℕ, gammaPTerm a y (i + N)‖ ≤ ∑' i : ℕ, ‖gammaPTerm a y N‖ * (1 / 2) ^ i :=
        tsum_of_norm_bounded hs.hasSum hgeom
    _ = 2 * ‖gammaPTerm a y N‖ := by rw [tsum_mul_left, tsum_geometric_two]; ring

end ZetaF
