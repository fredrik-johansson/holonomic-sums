/-
# Uniform Gamma bounds

* `rpow_le_exp_mul_Gamma`: `y^x ≤ e^y Γ(x+1)` for `y ≥ 0`, `x > 0`.
* `gammaRatio_bounded`: `Γ(Re w)·|1/Γ(w)|` is bounded on `{Re w ≥ 1, |Im w| ≤ Y}`.  This is a weak, but
  uniform, form of estimate (G1) of Appendix A.9, enough for local uniform convergence in `s`.
-/
import ZetaF.GammaBounds
import ZetaF.Holonomic.GammaTwist

open MeasureTheory Set Filter Finset
open scoped Real

namespace ZetaF

/-- `y^x ≤ e^y Γ(x+1)` for `y ≥ 0`, `x > 0`. -/
lemma rpow_le_exp_mul_Gamma {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    y ^ x ≤ rexp y * Real.Gamma (x + 1) := by
  rcases eq_or_lt_of_le hy with rfl | hy
  · rw [Real.zero_rpow hx.ne']; positivity
  have h1 : ∫ t in (0 : ℝ)..y, t ^ (x - 1) = y ^ x / x := by
    rw [integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]; simp
  have hint : IntegrableOn (fun t => rexp (-t) * t ^ (x - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hx
  have h2 : ∫ t in (0 : ℝ)..y, t ^ (x - 1) ≤ rexp y * Real.Gamma x := by
    rw [Real.Gamma_eq_integral hx, ← integral_const_mul, intervalIntegral.integral_of_le hy.le]
    calc ∫ t in Ioc 0 y, t ^ (x - 1) ≤ ∫ t in Ioc 0 y, rexp y * (rexp (-t) * t ^ (x - 1)) := by
          apply setIntegral_mono_on
          · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).1
              (intervalIntegral.intervalIntegrable_rpow' (by linarith)))
          · exact (hint.mono_set Ioc_subset_Ioi_self).const_mul _
          · exact measurableSet_Ioc
          · intro t ht
            rw [← mul_assoc, ← Real.exp_add]
            apply le_mul_of_one_le_left (Real.rpow_nonneg ht.1.le _)
            rw [Real.one_le_exp_iff]; linarith [ht.2]
      _ ≤ ∫ t in Ioi 0, rexp y * (rexp (-t) * t ^ (x - 1)) := by
          apply setIntegral_mono_set (hint.const_mul _)
          · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
            exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le
              (Real.rpow_nonneg (le_of_lt ht) _))
          · exact Eventually.of_forall Ioc_subset_Ioi_self
  rw [h1, div_le_iff₀ hx] at h2
  rw [Real.Gamma_add_one hx.ne']
  linarith

lemma continuousOn_gammaRatio : ContinuousOn gammaRatio {w : ℂ | 0 < w.re} := by
  intro w hw
  apply ContinuousAt.continuousWithinAt
  unfold gammaRatio
  apply ContinuousAt.mul
  · have : ContinuousAt Real.Gamma w.re := (Real.differentiableAt_Gamma fun m h => by
      have : (0 : ℝ) < w.re := hw
      have h' : (-(m : ℝ)) ≤ 0 := by simp
      linarith).continuousAt
    exact this.comp Complex.continuous_re.continuousAt
  · exact (Complex.differentiable_one_div_Gamma.continuous.norm).continuousAt

/-- `Γ(Re w)·|1/Γ(w)|` is bounded on `{Re w ≥ 1, |Im w| ≤ Y}`. -/
lemma gammaRatio_bounded (Y : ℝ) : ∃ C, ∀ w : ℂ, 1 ≤ w.re → |w.im| ≤ Y → gammaRatio w ≤ C := by
  set K := {w : ℂ | 1 ≤ w.re ∧ w.re ≤ 2 ∧ |w.im| ≤ Y}
  have hK : IsCompact K := by
    have : K = Complex.equivRealProd ⁻¹' (Set.Icc 1 2 ×ˢ Set.Icc (-Y) Y) := by
      ext w; simp [K, abs_le, Complex.equivRealProd]; tauto
    rw [this]
    exact (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage).2
      (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuousOn_gammaRatio.mono fun w hw => by simp only [mem_ofPred_eq]; linarith [hw.1])
  refine ⟨C, fun w h1 hY => ?_⟩
  set m := ⌊w.re⌋₊ - 1
  have hm1 : (m : ℝ) ≤ w.re - 1 := by
    have := Nat.floor_le (show 0 ≤ w.re by linarith)
    have h1' : 1 ≤ ⌊w.re⌋₊ := Nat.le_floor (by simpa using h1)
    simp only [m]; push_cast [Nat.cast_sub h1']; linarith
  have hm2 : w.re - 2 < m := by
    have := Nat.lt_floor_add_one w.re
    have h1' : 1 ≤ ⌊w.re⌋₊ := Nat.le_floor (by simpa using h1)
    simp only [m]; push_cast [Nat.cast_sub h1']; linarith
  have hw' : w - m ∈ K := by
    refine ⟨by simp; linarith, by simp; linarith, by simpa using hY⟩
  have := gammaRatio_add_nat_le (w := w - m) (by simp; linarith) m
  rw [sub_add_cancel] at this
  exact this.trans ((le_abs_self _).trans (by
    have := hC _ hw'; rwa [Real.norm_eq_abs] at this))

end ZetaF
