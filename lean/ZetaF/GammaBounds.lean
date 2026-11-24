/-
# Elementary bounds for the Gamma function

* `Γ(Re w)/|Γ(w)|` is nonincreasing under `w ↦ w + 1` (for `Re w > 0`).  This is a weak but
  elementary substitute for estimate (G1) of Appendix A.9 (`|1/Γ(w)| ≤ e^{π|Im w|/2}/Γ(Re w)`), and
  suffices for all convergence statements in §3 at a fixed `s`.
* `∑ q^n / Γ((σ+n)/2)` converges for every `q` (the kernel `E_s` of (6) is entire).
-/
import ZetaF.Deps

open Complex Filter Finset

namespace ZetaF

/-- The ratio `Γ(Re w) · |1/Γ(w)|`. -/
noncomputable def gammaRatio (w : ℂ) : ℝ := Real.Gamma w.re * ‖(Gamma w)⁻¹‖

lemma gammaRatio_nonneg {w : ℂ} (hw : 0 < w.re) : 0 ≤ gammaRatio w :=
  mul_nonneg (Real.Gamma_pos_of_pos hw).le (norm_nonneg _)

lemma gammaRatio_add_one_le {w : ℂ} (hw : 0 < w.re) : gammaRatio (w + 1) ≤ gammaRatio w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hG : Gamma w ≠ 0 := Gamma_ne_zero_of_re_pos hw
  unfold gammaRatio
  rw [add_re, one_re, Real.Gamma_add_one hw.ne', Gamma_add_one w hw0, mul_inv, norm_mul,
    norm_inv]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hle : w.re ≤ ‖w‖ := re_le_norm w
  have hGr := Real.Gamma_pos_of_pos hw
  have : w.re * ‖w‖⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hn]; exact hle
  calc w.re * Real.Gamma w.re * (‖w‖⁻¹ * ‖(Gamma w)⁻¹‖)
      = (w.re * ‖w‖⁻¹) * (Real.Gamma w.re * ‖(Gamma w)⁻¹‖) := by ring
    _ ≤ 1 * (Real.Gamma w.re * ‖(Gamma w)⁻¹‖) :=
        mul_le_mul_of_nonneg_right this (mul_nonneg hGr.le (norm_nonneg _))
    _ = _ := one_mul _

lemma gammaRatio_add_nat_le {w : ℂ} (hw : 0 < w.re) (m : ℕ) :
    gammaRatio (w + m) ≤ gammaRatio w := by
  induction m with
  | zero => simp
  | succ m ih =>
    have : 0 < (w + m).re := by simp; positivity
    calc gammaRatio (w + (m + 1 : ℕ)) = gammaRatio (w + m + 1) := by push_cast; ring_nf
      _ ≤ gammaRatio (w + m) := gammaRatio_add_one_le this
      _ ≤ _ := ih

/-- For `Re s > 0` the numbers `|1/Γ((s+n)/2)| · Γ((Re s + n)/2)` are bounded in `n`. -/
lemma norm_inv_Gamma_half_le {s : ℂ} (hs : 0 < s.re) :
    ∃ B, 0 ≤ B ∧ ∀ n : ℕ, ‖(Gamma ((s + n) / 2))⁻¹‖ * Real.Gamma ((s.re + n) / 2) ≤ B := by
  refine ⟨max (gammaRatio (s / 2)) (gammaRatio ((s + 1) / 2)),
    le_max_of_le_left (gammaRatio_nonneg (by simp; positivity)), fun n => ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := gammaRatio_add_nat_le (w := s / 2) (by simp; positivity) m
    have e : s / 2 + (m : ℂ) = (s + ((2 * m : ℕ) : ℂ)) / 2 := by push_cast; ring
    rw [e] at h
    refine le_trans (le_of_eq ?_) (h.trans (le_max_left _ _))
    unfold gammaRatio
    rw [mul_comm]; congr 2
    simp
  · have h := gammaRatio_add_nat_le (w := (s + 1) / 2) (by simp; positivity) m
    have e : (s + 1) / 2 + (m : ℂ) = (s + ((2 * m + 1 : ℕ) : ℂ)) / 2 := by push_cast; ring
    rw [e] at h
    refine le_trans (le_of_eq ?_) (h.trans (le_max_right _ _))
    unfold gammaRatio
    rw [mul_comm]; congr 2
    simp

/-- `∑_m q^m/Γ(y+m)` converges for `y > 0`. -/
lemma summable_pow_div_Gamma_add {y q : ℝ} (hy : 0 < y) (hq : 0 ≤ q) :
    Summable fun m : ℕ => q ^ m / Real.Gamma (y + m) := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * q)
  refine eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  have hym : 0 < y + m := by positivity
  have hG := Real.Gamma_pos_of_pos hym
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  rw [show y + ((m : ℝ) + 1) = (y + m) + 1 by ring, Real.Gamma_add_one hym.ne', pow_succ]
  rw [show q ^ m * q / ((y + m) * Real.Gamma (y + m)) = (q / (y + m)) * (q ^ m / Real.Gamma (y + m))
    by field_simp]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [div_le_iff₀ hym]
  have : (N : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- `∑_n q^n/Γ((σ+n)/2)` converges for `σ > 0`. -/
lemma summable_pow_div_Gamma_half {σ q : ℝ} (hσ : 0 < σ) (hq : 0 ≤ q) :
    Summable fun n : ℕ => q ^ n / Real.Gamma ((σ + n) / 2) := by
  apply Summable.even_add_odd
  · refine (summable_pow_div_Gamma_add (y := σ / 2) (q := q ^ 2) (by positivity) (by positivity)).congr
      fun m => ?_
    rw [← pow_mul]; congr 2; push_cast; ring
  · refine ((summable_pow_div_Gamma_add (y := (σ + 1) / 2) (q := q ^ 2) (by positivity)
      (by positivity)).mul_left q).congr fun m => ?_
    rw [← pow_mul, mul_div_assoc', ← pow_succ']; congr 2; push_cast; ring

end ZetaF
