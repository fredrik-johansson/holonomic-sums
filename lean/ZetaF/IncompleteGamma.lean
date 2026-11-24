/-
# Upper incomplete gamma function and the recurrence for `Q`

For `x > 0` and every `a ∈ ℂ`, `Γ(a, x) = ∫_x^∞ t^{a-1} e^{-t} dt` and
`Q(a, x) = Γ(a, x)/Γ(a)` (with `1/Γ = 0` at the poles, so `Q` is entire in `a`).  We prove
`Γ(a+1, x) = a Γ(a, x) + x^a e^{-x}` and hence `Q(a+1, x) = Q(a, x) + x^a e^{-x}/Γ(a+1)`
(paper §3.4 after Proposition 3.6, and Appendix A.4), for all `a ∈ ℂ`.
-/
import ZetaF.Holonomic.GammaTwist

open MeasureTheory Set Filter Topology
open scoped Real

namespace ZetaF

/-- Upper incomplete gamma function `Γ(a, x) = ∫_x^∞ t^{a-1} e^{-t} dt` (for `x > 0`). -/
noncomputable def upperGamma (a : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi x, (t : ℂ) ^ (a - 1) * (rexp (-t) : ℂ)

/-- Regularized upper incomplete gamma function `Q(a, x) = Γ(a, x)/Γ(a)`. -/
noncomputable def gammaQ (a : ℂ) (x : ℝ) : ℂ := upperGamma a x * (Complex.Gamma a)⁻¹

lemma integrableOn_cpow_mul_exp_Ioi (a : ℂ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * (rexp (-t) : ℂ)) (Ioi x) := by
  set r := a.re - 1
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (a - 1) * (rexp (-t) : ℂ))
      (volume.restrict (Ioi x)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := hx.trans ht
    apply ContinuousAt.continuousWithinAt
    exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 ht0)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt
  have hnorm : ∀ t ∈ Ioi x, ‖(t : ℂ) ^ (a - 1) * (rexp (-t) : ℂ)‖ = t ^ r * rexp (-t) := by
    intro t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans ht), Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    simp [r]
  rcases le_or_gt 0 r with hr | hr
  · have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := r) (p := 1) (b := 1) (by linarith)
      one_pos one_pos).mono_set (Ioi_subset_Ioi hx.le)
    refine Integrable.mono' h hmeas ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => ?_))
    rw [hnorm t ht]; simp
  · have h : IntegrableOn (fun t : ℝ => x ^ r * rexp (-t)) (Ioi x) :=
      (integrableOn_exp_neg_Ioi x).const_mul _
    refine Integrable.mono' h hmeas ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => ?_))
    rw [hnorm t ht]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx (le_of_lt ht) hr.le)
      (Real.exp_pos _).le

/-- `Γ(a+1, x) = a Γ(a, x) + x^a e^{-x}` for every `a ∈ ℂ` and `x > 0`. -/
theorem upperGamma_add_one (a : ℂ) {x : ℝ} (hx : 0 < x) :
    upperGamma (a + 1) x = a * upperGamma a x + (x : ℂ) ^ a * (rexp (-x) : ℂ) := by
  set f : ℝ → ℂ := fun t => -((t : ℂ) ^ a * (rexp (-t) : ℂ)) with hf
  set f' : ℝ → ℂ := fun t => -(a * ((t : ℂ) ^ (a - 1) * (rexp (-t) : ℂ))) +
    (t : ℂ) ^ (a + 1 - 1) * (rexp (-t) : ℂ) with hf'
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt f (f' t) t := by
    intro t ht
    have ht0 : 0 < t := hx.trans ht
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ a) (a * (t : ℂ) ^ (a - 1)) t := by
      simpa using ((hasDerivAt_id (t : ℂ)).cpow_const (c := a)
        (Complex.ofReal_mem_slitPlane.2 ht0)).comp_ofReal
    have h2 : HasDerivAt (fun y : ℝ => (rexp (-y) : ℂ)) ((-rexp (-t) : ℝ) : ℂ) t := by
      apply HasDerivAt.ofReal_comp
      simpa using (hasDerivAt_neg t).exp
    convert (h1.mul h2).neg using 1
    simp only [hf', add_sub_cancel_right]
    push_cast; ring
  have hint : IntegrableOn f' (Ioi x) := by
    refine (((integrableOn_cpow_mul_exp_Ioi a hx).const_mul a).neg.add
      (integrableOn_cpow_mul_exp_Ioi (a + 1) hx))
  have hlim : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a.re 1 one_pos
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [hf, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    simp
  have hcont : ContinuousWithinAt f (Ici x) x := by
    apply ContinuousAt.continuousWithinAt
    exact (((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 hx)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt).neg
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  simp only [hf', hf] at hftc
  have i1 : IntegrableOn (fun t : ℝ => -(a * ((t : ℂ) ^ (a - 1) * (rexp (-t) : ℂ)))) (Ioi x) :=
    ((integrableOn_cpow_mul_exp_Ioi a hx).const_mul a).neg
  rw [integral_add i1 (integrableOn_cpow_mul_exp_Ioi (a + 1) hx), integral_neg,
    integral_const_mul] at hftc
  unfold upperGamma
  simp only [zero_sub, neg_neg] at hftc
  linear_combination hftc

/-- **`Q(a+1, x) = Q(a, x) + x^a e^{-x}/Γ(a+1)`** for every `a ∈ ℂ`, `x > 0`. -/
theorem gammaQ_add_one (a : ℂ) {x : ℝ} (hx : 0 < x) :
    gammaQ (a + 1) x = gammaQ a x + (x : ℂ) ^ a * (rexp (-x) : ℂ) * (Complex.Gamma (a + 1))⁻¹ := by
  unfold gammaQ
  rw [upperGamma_add_one a hx, add_mul, mul_assoc, ← mul_inv_Gamma_add_one a]; ring

end ZetaF
