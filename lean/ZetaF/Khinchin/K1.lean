/-
# Formula (K1) for Khinchin's constant

`log K = -Z'(0)`, where `Z(s) = ∑_{k ≥ 1} μ_k k^{-s}` is the Khinchin zeta function
(`khinchinZ`, a function of complex `s`). We identify `Z` with the L-series of `μ` and use
Mathlib's differentiation of L-series inside the half-plane of absolute convergence.
-/
import ZetaF.Khinchin.LogK

open Filter Topology Real Complex LSeries

namespace ZetaF

/-- The Gauss–Kuzmin probabilities as an arithmetic function `ℕ → ℂ` (`gkMu 0 = 0`). -/
noncomputable def gkMuC (n : ℕ) : ℂ := (gkMu n : ℂ)

lemma khinchinZ_eq_LSeries (s : ℂ) : khinchinZ s = LSeries gkMuC s := by
  rw [khinchinZ, LSeries, ← (Nat.succ_injective).tsum_eq (f := fun n => term gkMuC s n)]
  · refine tsum_congr fun k => ?_
    rw [term_of_ne_zero (Nat.succ_ne_zero k), gkMuC, div_eq_mul_inv, ← Complex.cpow_neg]
  · intro n hn
    rcases n with _ | n
    · exact absurd (term_zero _ _) hn
    · exact ⟨n, rfl⟩

lemma gkMu_le (n : ℕ) (hn : n ≠ 0) : gkMu n ≤ 1 / Real.log 2 * (n : ℝ) ^ (-2 : ℝ) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hx : (0 : ℝ) < 1 / ((n : ℝ) * (n + 2)) := by positivity
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / ((n : ℝ) * (n + 2)) by linarith)
  have h2 : 1 / ((n : ℝ) * (n + 2)) ≤ 1 / (n : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have e : 1 / Real.log 2 * (n : ℝ) ^ (-2 : ℝ) = (1 / (n : ℝ) ^ 2) / Real.log 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]; ring
  rw [gkMu, e]
  exact div_le_div_of_nonneg_right (by linarith) hl.le

lemma abscissaOfAbsConv_gkMuC : abscissaOfAbsConv gkMuC < (0 : ℂ).re := by
  have h : abscissaOfAbsConv gkMuC ≤ ((-2 : ℝ) + 1 : ℝ) := by
    refine abscissaOfAbsConv_le_of_le_const_mul_rpow ⟨1 / Real.log 2, fun n hn => ?_⟩
    rw [gkMuC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · exact gkMu_le n hn
    · rcases n with _ | n
      · exact absurd rfl hn
      · exact gkMu_nonneg n
  refine h.trans_lt ?_
  rw [Complex.zero_re]
  exact_mod_cast (by norm_num : (-2 : ℝ) + 1 < 0)

lemma LSeries_logMul_gkMuC_zero : LSeries (logMul gkMuC) 0 = (logK : ℂ) := by
  rw [LSeries, ← (Nat.succ_injective).tsum_eq (f := fun n => term (logMul gkMuC) 0 n), logK,
    Complex.ofReal_tsum]
  · refine tsum_congr fun k => ?_
    rw [term_of_ne_zero (Nat.succ_ne_zero k), Complex.cpow_zero, div_one, logMul, gkMuC,
      ← Complex.natCast_log, mul_comm]
    push_cast
    rfl
  · intro n hn
    rcases n with _ | n
    · exact absurd (term_zero _ _) hn
    · exact ⟨n, rfl⟩

/-- **(K1)**: `Z'(0) = -log K`. -/
theorem hasDerivAt_khinchinZ_zero : HasDerivAt khinchinZ (-(logK : ℂ)) 0 := by
  rw [funext khinchinZ_eq_LSeries, ← LSeries_logMul_gkMuC_zero]
  exact LSeries_hasDerivAt abscissaOfAbsConv_gkMuC

/-- **(K1)**: `log K = -Z'(0)`. -/
theorem logK_eq_neg_deriv_khinchinZ : (logK : ℂ) = -deriv khinchinZ 0 := by
  rw [hasDerivAt_khinchinZ_zero.deriv, neg_neg]

end ZetaF
