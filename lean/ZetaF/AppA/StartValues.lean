/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Starting values (Appendix A, lemma L6)

The starting values of the bit-burst evaluation of a dual term are series `∑_j g_j D_{a+j}(c₀)`. By
the recurrence (14) (`momentD_rec`), each `D_{a+n}` reduces to the base value of its class:
`D_{a+n} = α_n D_a + β_n E` with `α_n = (-c)^n/(a+1)_n` (`momentD_add_nat_eq`), for every complex `a`
with `a + 1 + i ≠ 0`. The cancellation in the weighted sums is controlled by
`∑ x^n/(n!)² ≤ e^{2√x}` (`sum_pow_div_factorial_sq_le`): with `|g_j| ≤ C R^{2j}/|Γ(j + σ₀)|` the terms
of `∑ g_j α_j` are of size `(R² c₀)^j/(j!)²` up to factors polynomial in `j`, so the series loses at
most `2R√c₀ log₂ e + O(log p)` bits.
-/
import ZetaF.Holonomic.DualMoments
import Mathlib.Data.Nat.Choose.Central

open Finset Real
open scoped Nat

namespace ZetaF.AppA

/-- `α_n = (-c)^n/(a+1)_n`. -/
noncomputable def alphaD (a : ℂ) (c : ℝ) (n : ℕ) : ℂ := (-(c : ℂ)) ^ n / ∏ i ∈ range n, (a + 1 + i)

/-- `β_0 = 0`, `β_{n+1} = (u₀^{a+n+1} - c β_n)/(a+n+1)`. -/
noncomputable def betaD (a : ℂ) (u₀ c : ℝ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => ((u₀ : ℂ) ^ (a + n + 1) - c * betaD a u₀ c n) / (a + 1 + n)

lemma alphaD_succ (a : ℂ) (c : ℝ) (n : ℕ) (ha : a + 1 + n ≠ 0) :
    alphaD a c (n + 1) = -(c : ℂ) * alphaD a c n / (a + 1 + n) := by
  unfold alphaD
  rw [prod_range_succ, pow_succ]
  rcases eq_or_ne (∏ i ∈ range n, (a + 1 + i)) 0 with hP | hP
  · rw [hP]; simp
  · field_simp

/-- **`D_{a+n} = α_n D_a + β_n E`** for complex `a` with `a + 1 + i ≠ 0` (`i < n`). -/
theorem momentD_add_nat_eq {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (a : ℂ)
    (ha : ∀ i : ℕ, a + 1 + i ≠ 0) (n : ℕ) :
    momentD u₀ c (a + n) =
      alphaD a c n * momentD u₀ c a + betaD a u₀ c n * (rexp (-(c / u₀)) : ℂ) := by
  induction n with
  | zero => simp [alphaD, betaD]
  | succ n ih =>
    have hrec := momentD_rec hc hu₀ (a + n + 1)
    rw [show a + n + 1 - 1 = a + n by ring, ih] at hrec
    have hne : a + 1 + n ≠ 0 := ha n
    have hD : momentD u₀ c (a + (n + 1 : ℕ)) = ((rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (a + n + 1) -
        c * (alphaD a c n * momentD u₀ c a + betaD a u₀ c n * (rexp (-(c / u₀)) : ℂ))) /
        (a + 1 + n) := by
      rw [eq_div_iff hne, show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring]
      linear_combination hrec
    rw [hD, alphaD_succ a c n hne, betaD]
    field_simp
    ring

/-- `|α_n| = c^n/|(a+1)_n|`. -/
lemma norm_alphaD (a : ℂ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ‖alphaD a c n‖ = c ^ n / ‖∏ i ∈ range n, (a + 1 + i)‖ := by
  unfold alphaD
  rw [norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc]

/-- `(2n)! ≤ 4^n (n!)²`. -/
lemma factorial_two_mul_le (n : ℕ) : (2 * n)! ≤ 4 ^ n * (n !) ^ 2 := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega)
  rw [show 2 * n - n = n by omega, ← Nat.centralBinom_eq_two_mul_choose] at h
  rw [← h, mul_assoc, sq]
  exact Nat.mul_le_mul_right _ (Nat.centralBinom_le_four_pow n)

/-- **`∑ x^n/(n!)² ≤ e^{2√x}`** (summable), for `x ≥ 0`. -/
theorem sum_pow_div_factorial_sq_le {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => x ^ n / ((n ! : ℝ) ^ 2)) ∧
      ∑' n : ℕ, x ^ n / ((n ! : ℝ) ^ 2) ≤ Real.exp (2 * √x) := by
  set y := 2 * √x
  have hy : 0 ≤ y := by positivity
  have hexp : HasSum (fun m : ℕ => y ^ m / (m ! : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have hsub : Summable fun n : ℕ => y ^ (2 * n) / ((2 * n)! : ℝ) :=
    hexp.summable.comp_injective (i := fun n : ℕ => 2 * n) (fun a b h => by simp only at h; omega)
  have hle : ∀ n : ℕ, x ^ n / ((n ! : ℝ) ^ 2) ≤ y ^ (2 * n) / ((2 * n)! : ℝ) := by
    intro n
    have hy2 : y ^ (2 * n) = 4 ^ n * x ^ n := by
      rw [pow_mul, show y ^ 2 = 4 * x by simp only [y]; rw [mul_pow, sq_sqrt hx]; norm_num, mul_pow]
    rw [hy2]
    have hf : ((2 * n)! : ℝ) ≤ 4 ^ n * (n ! : ℝ) ^ 2 := by exact_mod_cast factorial_two_mul_le n
    have hf0 : (0 : ℝ) < ((2 * n)! : ℝ) := by positivity
    have hn0 : (0 : ℝ) < (n ! : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hn0 hf0]
    have hxn : 0 ≤ x ^ n := pow_nonneg hx n
    nlinarith [mul_le_mul_of_nonneg_left hf hxn]
  have hs : Summable fun n : ℕ => x ^ n / ((n ! : ℝ) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hsub
  refine ⟨hs, (hs.tsum_le_tsum hle hsub).trans ?_⟩
  rw [← hexp.tsum_eq]
  exact tsum_comp_le_tsum_of_inj (f := fun m : ℕ => y ^ m / (m ! : ℝ)) hexp.summable
    (fun m => by positivity) (i := fun n : ℕ => 2 * n) (fun a b h => by simp only at h; omega)

end ZetaF.AppA
