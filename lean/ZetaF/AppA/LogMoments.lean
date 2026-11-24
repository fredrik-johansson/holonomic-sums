/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Log-moments for the derivatives in `s` (Appendix A, lemma L9)

The jets in `s` of the dual terms need the moments
`Z^{(i)}_t[g](c) = ∫_0^{u₀} u^{-t} (log u)^i e^{-c/u} g(u) du`, which satisfy (integration by parts)

`c Z^{(i+1)}_{t+1}[g] = E u₀^{1-t} (log u₀)^{i+1} g(u₀) - (1-t) Z^{(i+1)}_t[g] - Z^{(i+1)}_t[θg] - (i+1) Z^{(i)}_t[g]`,

`E = e^{-c/u₀}`, `θg = u g'` (`dualMomentLog_ibp`). This extends `dualMoment_ibp` (the case `i + 1 = 0`)
to the factor `(log u)^{i+1}`, which is not differentiable at `0`; the weight `e^{-c/u}` makes everything
continuous there.
-/
import ZetaF.Holonomic.DualMoments

open MeasureTheory Set Filter Real
open scoped Topology

namespace ZetaF.AppA

/-- `Z^{(i)}_t[g] = ∫_0^{u₀} u^{-t} (log u)^i e^{-c/u} g(u) du`. -/
noncomputable def dualMomentLog (u₀ c : ℝ) (t : ℂ) (i : ℕ) (g : ℝ → ℂ) : ℂ :=
  dualMoment u₀ c t fun u => (Real.log u : ℂ) ^ i * g u

/-- `u^{-t} e^{-c/u} (log u)^j` (extended by `0` for `u ≤ 0`) is continuous. -/
lemma continuous_dualWeight_mul_log {c : ℝ} (hc : 0 < c) (t : ℂ) (j : ℕ) :
    Continuous fun u : ℝ => dualWeight c t u * (Real.log u : ℂ) ^ j := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [gt_mem_nhds hu] with y hy
    rw [dualWeight, if_neg (not_lt.2 hy.le), zero_mul]
  · have h0 : dualWeight c t 0 * (Real.log 0 : ℂ) ^ j = 0 := by simp [dualWeight]
    rw [ContinuousAt, h0]
    -- `‖w_t(u) (log u)^j‖ ≤ ‖w_{t+j}(u)‖` for `0 < u ≤ 1`, and `= 0` for `u ≤ 0`
    have hT := tendsto_dualWeight_zero hc (t + j)
    rw [tendsto_zero_iff_norm_tendsto_zero] at hT ⊢
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hT
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
    rcases le_or_gt y 0 with hy0 | hy0
    · simp [dualWeight, not_lt.2 hy0]
    · have hw : dualWeight c t y = dualWeight c (t + j) y * (y : ℂ) ^ j := by
        have := dualWeight_sub_nat (c := c) (t + j) j hy0
        rwa [add_sub_cancel_right] at this
      rw [hw, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hy0.le, mul_assoc, ← mul_pow]
      have hlog : y * ‖Real.log y‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos hy0.le hy.le)]
        have := Real.log_le_sub_one_of_pos (inv_pos.2 hy0)
        rw [Real.log_inv] at this
        have h1 : y * (y⁻¹ - 1) ≤ 1 := by
          rw [mul_sub, mul_inv_cancel₀ hy0.ne']; linarith
        nlinarith
      have hp : (y * ‖Real.log y‖) ^ j ≤ 1 := pow_le_one₀ (by positivity) hlog
      calc ‖dualWeight c (t + j) y‖ * (y * ‖Real.log y‖) ^ j ≤ ‖dualWeight c (t + j) y‖ * 1 :=
            mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ = _ := mul_one _
  · have hlog : ContinuousAt (fun y : ℝ => (Real.log y : ℂ)) u :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hu.ne')
    exact (continuous_dualWeight hc t).continuousAt.mul (hlog.pow j)

/-- **The log-moment recurrence** (Appendix A, derivatives in `s`). -/
theorem dualMomentLog_ibp {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (t : ℂ) (i : ℕ)
    {g g' : ℝ → ℂ} (hg : ∀ u ∈ Icc 0 u₀, HasDerivAt g (g' u) u) (hg' : ContinuousOn g' (Icc 0 u₀)) :
    c * dualMomentLog u₀ c (t + 1) (i + 1) g =
      (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (1 - t) * (Real.log u₀ : ℂ) ^ (i + 1) * g u₀ -
        (1 - t) * dualMomentLog u₀ c t (i + 1) g -
        dualMomentLog u₀ c t (i + 1) (fun u => u * g' u) -
        (i + 1) * dualMomentLog u₀ c t i g := by
  have hgc : ContinuousOn g (Icc 0 u₀) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  set L : ℝ → ℂ := fun u => (Real.log u : ℂ)
  set F : ℝ → ℂ := fun u => (u : ℂ) * (dualWeight c t u * L u ^ (i + 1)) * g u with hF
  set F' : ℝ → ℂ := fun u =>
    (1 - t) * (dualWeight c t u * (L u ^ (i + 1) * g u)) +
      c * (dualWeight c (t + 1) u * (L u ^ (i + 1) * g u)) +
      dualWeight c t u * (L u ^ (i + 1) * (u * g' u)) +
      (i + 1) * (dualWeight c t u * (L u ^ i * g u)) with hF'
  have hderiv : ∀ u ∈ Ioo 0 u₀, HasDerivAt F (F' u) u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu0.ne'
    have hL : HasDerivAt L ((u : ℂ)⁻¹) u := by
      have := (Real.hasDerivAt_log hu0.ne').ofReal_comp
      simpa [L] using this
    have hLp : HasDerivAt (fun y => L y ^ (i + 1)) (((i + 1 : ℕ) : ℂ) * L u ^ i * (u : ℂ)⁻¹) u := by
      convert hL.pow (i + 1) using 1
      simp
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := u)).mul
      ((hasDerivAt_dualWeight (c := c) t hu0).mul hLp)).mul (hg u (Ioo_subset_Icc_self hu))
    convert h1 using 1
    · funext v; simp only [hF, Pi.mul_apply, Complex.ofRealCLM_apply]
    · simp only [hF', Complex.ofRealCLM_apply, dualWeight_add_one t hu0, Pi.mul_apply]
      push_cast
      field_simp
      ring
  have hw := continuous_dualWeight_mul_log hc t
  have hw1 := continuous_dualWeight_mul_log hc (t + 1)
  have hcontF : ContinuousOn F (Icc 0 u₀) :=
    ((Complex.continuous_ofReal.mul (hw (i + 1))).continuousOn).mul hgc
  have hI : ∀ {f : ℝ → ℂ}, ContinuousOn f (Icc 0 u₀) → IntervalIntegrable f volume 0 u₀ :=
    fun hf => (hf.mono (by rw [uIcc_of_le hu₀.le])).intervalIntegrable
  have assoc : ∀ (s' : ℂ) (j : ℕ) (h : ℝ → ℂ) (u : ℝ),
      dualWeight c s' u * (L u ^ j * h u) = (dualWeight c s' u * L u ^ j) * h u := fun _ _ _ _ => by ring
  have i1 : IntervalIntegrable (fun u => dualWeight c t u * (L u ^ (i + 1) * g u)) volume 0 u₀ := by
    simp_rw [assoc]; exact hI ((hw (i + 1)).continuousOn.mul hgc)
  have i2 : IntervalIntegrable (fun u => dualWeight c (t + 1) u * (L u ^ (i + 1) * g u)) volume 0 u₀ := by
    simp_rw [assoc]; exact hI ((hw1 (i + 1)).continuousOn.mul hgc)
  have i3 : IntervalIntegrable (fun u => dualWeight c t u * (L u ^ (i + 1) * (u * g' u))) volume 0 u₀ := by
    have e : (fun u => dualWeight c t u * (L u ^ (i + 1) * ((u : ℂ) * g' u))) =
        fun u => (dualWeight c t u * L u ^ (i + 1)) * ((u : ℂ) * g' u) := by funext u; ring
    rw [e]
    exact hI ((hw (i + 1)).continuousOn.mul (Complex.continuous_ofReal.continuousOn.mul hg'))
  have i4 : IntervalIntegrable (fun u => dualWeight c t u * (L u ^ i * g u)) volume 0 u₀ := by
    simp_rw [assoc]; exact hI ((hw i).continuousOn.mul hgc)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu₀.le hcontF hderiv
    ((((i1.const_mul _).add (i2.const_mul _)).add i3).add (i4.const_mul _))
  rw [intervalIntegral.integral_add (((i1.const_mul _).add (i2.const_mul _)).add i3) (i4.const_mul _),
    intervalIntegral.integral_add ((i1.const_mul _).add (i2.const_mul _)) i3,
    intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hftc
  have hF0 : F 0 = 0 := by simp [hF]
  have hFu₀ : F u₀ = (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (1 - t) * L u₀ ^ (i + 1) * g u₀ := by
    have hu' : (u₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu₀.ne'
    simp only [hF, dualWeight_of_pos hu₀]
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hu', Complex.cpow_one]; ring
  rw [hF0, sub_zero, hFu₀] at hftc
  unfold dualMomentLog dualMoment
  simp only [L] at hftc
  rw [← hftc]
  push_cast
  ring

end ZetaF.AppA
