/-
# Proposition 4.2, conditional on the kernel representation

The paper's proof of Proposition 4.2 rests on `∫₀^∞ e^{-x²u} h_s(u) du = e^{-τx^r} x^{-s}` (the damped
kernel is the inverse Laplace transform of `e^{-τ y^{r/2}} y^{-s/2}`, a Wright function), which it
justifies only briefly via Mellin transforms.  We take this representation and the integrability of
`h_s` near `0` and `∞` as hypotheses; the theta splitting (`theta_split`) and the termwise
expansions of `Kernel.lean` then give the identity with
`I_k = ∑_j c_j ∫_{u₀}^∞ e^{-k²u} u^{a_j-1}` and `J_m = ∑_j c_j D_{a_j-1/2}(π²m²)` (for `r < 1`).
-/
import ZetaF.Damped.Kernel
import ZetaF.Splitting.Abstract

open MeasureTheory Set Filter
open scoped Real Nat Topology

namespace ZetaF

/-- **Proposition 4.2 (conditional)**, for `0 < r < 1`. -/
theorem damped_split {τ r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℂ) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hcont : ContinuousOn (dampedKernel τ r s) (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖dampedKernel τ r s u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-u) * ‖dampedKernel τ r s u‖) (Ioi u₀))
    (hrep : ∀ k : ℕ, 1 ≤ k → ∫ u in Ioi 0, (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * dampedKernel τ r s u =
      (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * (k : ℂ) ^ (-s)) :
    dampedZetaF (fun _ => 1) s τ r =
      (∑' k : ℕ, ∑' j, dCoeff τ r s j * upperLaplace (((k + 1 : ℕ) : ℝ) ^ 2) u₀ (dExp s r j)) +
      √π * (∑' m : ℕ, ∑' j, dCoeff τ r s j *
        lowerDual (π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2) u₀ (dExp s r j)) +
      mainTerm (dampedKernel τ r s) u₀ 1 := by
  have hfar' : IntegrableOn (fun u => rexp (-(((1 : ℕ) : ℝ) ^ 2 * u)) * ‖dampedKernel τ r s u‖)
      (Ioi u₀) := by simpa using hfar
  have h := theta_split (le_refl 1) hu₀ hcont hnear hfar'
  have hk : ∀ k : ℕ, kTerm (dampedKernel τ r s) u₀ (k + 1) =
      ∑' j, dCoeff τ r s j * upperLaplace (((k + 1 : ℕ) : ℝ) ^ 2) u₀ (dExp s r j) := fun k =>
    ((hasSum_kTerm_damped hr0 (by linarith) s hu₀ (Nat.succ_pos k)).tsum_eq).symm
  have hm : ∀ m : ℕ, dualTerm (dampedKernel τ r s) u₀ (m + 1) =
      ∑' j, dCoeff τ r s j * lowerDual (π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2) u₀ (dExp s r j) :=
    fun m => ((hasSum_dualTerm_damped hr0 hr1 s hu₀ (Nat.succ_pos m)).tsum_eq).symm
  simp_rw [hk, hm] at h
  rw [← h.tsum_eq]
  unfold dampedZetaF LSeries
  rw [tsum_eq_zero_add']
  · rw [LSeries.term_zero, zero_add]
    refine tsum_congr fun k => ?_
    rw [hrep (k + 1) (by omega), LSeries.term_of_ne_zero (Nat.succ_ne_zero k), mul_one,
      div_eq_mul_inv, ← Complex.cpow_neg]
  · have := h.summable
    refine this.congr fun k => ?_
    rw [hrep (k + 1) (by omega), LSeries.term_of_ne_zero (Nat.succ_ne_zero k), mul_one,
      div_eq_mul_inv, ← Complex.cpow_neg]

end ZetaF
