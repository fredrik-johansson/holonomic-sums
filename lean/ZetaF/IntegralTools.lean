/-
# Small measure-theoretic helpers
-/
import ZetaF.Deps

open MeasureTheory Filter Finset

namespace ZetaF

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A pointwise summable series of nonnegative integrable functions whose integrals are summable
is integrable. -/
lemma integrable_tsum_of_nonneg {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (h0 : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x) (hpt : ∀ᵐ x ∂μ, Summable fun n => f n x)
    (hs : Summable fun n => ∫ x, f n x ∂μ) : Integrable (fun x => ∑' n, f n x) μ := by
  have hmeas : AEStronglyMeasurable (fun x => ∑' n, f n x) μ :=
    aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun N x => ∑ n ∈ range N, f n x)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hf n).1)
      (hpt.mono fun x hx => hx.hasSum.tendsto_sum_nat)
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (h0.mono fun x hx => tsum_nonneg hx)]
  have e : ∀ᵐ x ∂μ, ENNReal.ofReal (∑' n, f n x) = ∑' n, ENNReal.ofReal (f n x) :=
    (h0.and hpt).mono fun x hx => ENNReal.ofReal_tsum_of_nonneg hx.1 hx.2
  rw [lintegral_congr_ae e, lintegral_tsum fun n => (hf n).1.aemeasurable.ennreal_ofReal]
  have e2 : ∀ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ = ENNReal.ofReal (∫ x, f n x ∂μ) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hf n) (h0.mono fun x hx => hx n)).symm
  simp_rw [e2]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h0.mono fun x hx => hx n)) hs]
  exact ENNReal.ofReal_lt_top

end ZetaF
