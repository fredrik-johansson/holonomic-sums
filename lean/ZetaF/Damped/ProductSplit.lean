/-
# Proposition 4.3, conditional on the kernel representation

As for Proposition 4.2 (`damped_split`), we assume the kernel representation
`∫₀^∞ e^{-k²u} h(u) du = e^{-τk^r} F(k) k^{-s}` for `k ≥ k₀` (with `h = prodKernel a τ r s`, and `F(k)`
typically `evalInv a k = ∑ a_n k^{-n}`), the continuity of `h` and the integrability hypotheses of
`theta_split`.  The theta splitting then gives
`Λ_F^{≥k₀}(s;τ,r) = ∑_{k≥k₀} I_k + √π ∑_{m≥1} J_m + M`
with the `k`-terms as absolutely convergent double series (`0 < r < 2`, `k₀ > R`), and, for `0 < r < 1`,
also the dual terms as absolutely convergent double series.  The main term `M` is kept as the
integral `∫₀^{u₀} (½√(π/u) - ½ - ∑_{k<k₀} e^{-k²u}) h(u) du`.
-/
import ZetaF.Damped.Product
import ZetaF.Splitting.Abstract

open MeasureTheory Set Filter Finset
open scoped Real Nat Topology

namespace ZetaF

/-- The theta splitting of `Λ_F^{≥k₀}` for an abstract kernel `h` with the kernel representation. -/
lemma tail_damped_split_of_kernel {h : ℝ → ℂ} {F : ℕ → ℂ} {τ r : ℝ} (s : ℂ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖h u‖) (Ioi u₀))
    (hrep : ∀ k : ℕ, k₀ ≤ k → ∫ u in Ioi 0, (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * h u =
      (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k * (k : ℂ) ^ (-s)) :
    zetaTail (fun k => (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k) k₀ s =
      ∑' k : ℕ, kTerm h u₀ (k + k₀) + √π * ∑' m : ℕ, dualTerm h u₀ (m + 1) + mainTerm h u₀ k₀ := by
  have hth := theta_split hk₀ hu₀ hcont hnear hfar
  set G : ℕ → ℂ := fun k => (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k
  have hterm : ∀ n : ℕ, LSeries.term (tail k₀ G) s (n + k₀) =
      ∫ u in Ioi 0, (rexp (-(((n + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * h u := by
    intro n
    rw [hrep (n + k₀) (Nat.le_add_left _ _), LSeries.term_of_ne_zero (by omega)]
    simp only [tail, G, Nat.le_add_left, ite_true]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
  have hzero : ∑ i ∈ range k₀, LSeries.term (tail k₀ G) s i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rcases eq_or_ne i 0 with rfl | hi0
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero hi0]
      simp only [tail, not_le.2 (Finset.mem_range.1 hi), ite_false, zero_div]
  have hs : HasSum (LSeries.term (tail k₀ G) s)
      (∑' k : ℕ, kTerm h u₀ (k + k₀) + √π * ∑' m : ℕ, dualTerm h u₀ (m + 1) +
        mainTerm h u₀ k₀) := by
    rw [← hasSum_nat_add_iff' k₀, hzero, sub_zero]
    simpa only [hterm] using hth
  unfold zetaTail LSeries
  exact hs.tsum_eq

/-- **Proposition 4.3 (conditional), with `J_m` as integrals**, for `0 < r < 2`: the `k`-terms are
absolutely convergent double series over `(n, j)`. -/
theorem prod_damped_split_integral {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R)
    {F : ℕ → ℂ} {τ r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) (s : ℂ) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hRk₀ : R < k₀)
    (hcont : ContinuousOn (prodKernel a τ r s) (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖prodKernel a τ r s u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖prodKernel a τ r s u‖) (Ioi u₀))
    (hrep : ∀ k : ℕ, k₀ ≤ k →
      ∫ u in Ioi 0, (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * prodKernel a τ r s u =
        (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k * (k : ℂ) ^ (-s)) :
    zetaTail (fun k => (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k) k₀ s =
      (∑' k : ℕ, ∑' p : ℕ × ℕ, a p.1 * dCoeff τ r (s + p.1) p.2 *
          upperLaplace (((k + k₀ : ℕ) : ℝ) ^ 2) u₀ (dExp (s + p.1) r p.2)) +
      √π * ∑' m : ℕ, dualTerm (prodKernel a τ r s) u₀ (m + 1) +
      mainTerm (prodKernel a τ r s) u₀ k₀ := by
  rw [tail_damped_split_of_kernel s hu₀ hk₀ hcont hnear hfar hrep]
  congr 2
  refine tsum_congr fun k => ?_
  have hk : R < ((k + k₀ : ℕ) : ℝ) := hRk₀.trans_le (by exact_mod_cast Nat.le_add_left _ _)
  exact ((hasSum_kTerm_prod hR ha hr0 hr2 s hu₀ hk).tsum_eq).symm

/-- **Proposition 4.3 (conditional)**, for `0 < r < 1`: both the `k`-terms and the dual terms are
absolutely convergent double series over `(n, j)`. -/
theorem prod_damped_split {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R)
    {F : ℕ → ℂ} {τ r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℂ) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hRk₀ : R < k₀)
    (hcont : ContinuousOn (prodKernel a τ r s) (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖prodKernel a τ r s u‖) (Ioc 0 u₀))
    (hfar : IntegrableOn (fun u => rexp (-((k₀ : ℝ) ^ 2 * u)) * ‖prodKernel a τ r s u‖) (Ioi u₀))
    (hrep : ∀ k : ℕ, k₀ ≤ k →
      ∫ u in Ioi 0, (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * prodKernel a τ r s u =
        (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k * (k : ℂ) ^ (-s)) :
    zetaTail (fun k => (rexp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k) k₀ s =
      (∑' k : ℕ, ∑' p : ℕ × ℕ, a p.1 * dCoeff τ r (s + p.1) p.2 *
          upperLaplace (((k + k₀ : ℕ) : ℝ) ^ 2) u₀ (dExp (s + p.1) r p.2)) +
      √π * (∑' m : ℕ, ∑' p : ℕ × ℕ, a p.1 * dCoeff τ r (s + p.1) p.2 *
          lowerDual (π ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2) u₀ (dExp (s + p.1) r p.2)) +
      mainTerm (prodKernel a τ r s) u₀ k₀ := by
  rw [prod_damped_split_integral hR ha hr0 (by linarith) s hu₀ hk₀ hRk₀ hcont hnear hfar hrep]
  congr 3
  refine tsum_congr fun m => ?_
  exact ((hasSum_dualTerm_prod hR ha hr0 hr1 s hu₀ (Nat.succ_pos m)).tsum_eq).symm

end ZetaF
