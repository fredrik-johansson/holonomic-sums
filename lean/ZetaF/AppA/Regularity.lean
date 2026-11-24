/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Regularity of the multiplication cost (Appendix A, lemma L3)

The paper assumes the usual regularity conditions on the cost `𝖬(p)` of `p`-bit multiplication:
`𝖬(p)/p` nondecreasing and `𝖬(p log p) = O(𝖬(p) log p)`. Every "by the regularity of `𝖬`" step of
Appendix A uses two consequences, proved here:

* `𝖬(A n) = O(𝖬(n))` for every fixed `A ≥ 1` (`regular_scale`): with `g(n) = 𝖬(n)/n` nondecreasing and
  `2n ≤ n log₂ n` for `n ≥ 4`, `g(2n) ≤ g(n log n) ≤ C g(n)`;
* the binary-splitting bound `(log p + 1) 𝖬(A p (log p + 1)) = O(𝖬(p) log² p)` (`regular_cost`), the form
  in which "`O(𝖬(p log p) log p) = O(𝖬(p) log² p)`" is used.

Logarithms are `Nat.log 2`.
-/
import ZetaF.Deps

open Real

namespace ZetaF.AppA

section Regular

variable {M : ℕ → ℕ} (hdiv : ∀ a b, 0 < a → a ≤ b → M a * b ≤ M b * a)
  {C : ℕ} (hreg : ∀ n ≥ 4, M (n * Nat.log 2 n) ≤ C * M n * Nat.log 2 n)

/-- `g(n) = 𝖬(n)/n`. -/
noncomputable def gM (M : ℕ → ℕ) (n : ℕ) : ℝ := (M n : ℝ) / n

include hdiv in
lemma gM_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : gM M a ≤ gM M b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  unfold gM
  rw [div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)]
  exact_mod_cast hdiv a b ha hab

lemma two_le_log {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)

include hdiv in
/-- `𝖬` is monotone on positive arguments. -/
lemma M_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : M a ≤ M b := by
  have h := hdiv a b ha hab
  have h2 : M b * a ≤ M b * b := Nat.mul_le_mul_left _ hab
  exact Nat.le_of_mul_le_mul_right (h.trans h2) (lt_of_lt_of_le ha hab)

include hdiv hreg in
/-- `g(2n) ≤ C g(n)` for `n ≥ 4`. -/
lemma gM_double {n : ℕ} (hn : 4 ≤ n) : gM M (2 * n) ≤ C * gM M n := by
  have hL := two_le_log hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL0 : (0 : ℝ) < (Nat.log 2 n : ℝ) := by exact_mod_cast (by omega : 0 < Nat.log 2 n)
  have h1 := gM_mono hdiv (a := 2 * n) (b := n * Nat.log 2 n) (by omega) (by nlinarith)
  refine h1.trans ?_
  unfold gM
  have h2 : (M (n * Nat.log 2 n) : ℝ) ≤ C * M n * Nat.log 2 n := by exact_mod_cast hreg n hn
  push_cast
  rw [div_le_iff₀ (by positivity)]
  calc (M (n * Nat.log 2 n) : ℝ) ≤ C * M n * Nat.log 2 n := h2
    _ = C * ((M n : ℝ) / n) * (n * Nat.log 2 n) := by field_simp

include hdiv hreg in
lemma gM_pow_two {m : ℕ} (hm : 4 ≤ m) (j : ℕ) : gM M (2 ^ j * m) ≤ (C : ℝ) ^ j * gM M m := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h4 : 4 ≤ 2 ^ j * m := le_trans hm (Nat.le_mul_of_pos_left _ (by positivity))
    rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc]
    refine (gM_double hdiv hreg h4).trans ?_
    rw [pow_succ]
    have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    nlinarith

lemma le_two_pow_mul {A : ℕ} (hA : 1 ≤ A) : 2 * A ≤ 2 ^ A := by
  induction A, hA using Nat.le_induction with
  | base => norm_num
  | succ A hA ih => rw [pow_succ]; omega

include hdiv hreg in
/-- **`𝖬(A n) ≤ A Cᴬ 𝖬(n)`** for `A ≥ 1`, `n ≥ 4`. -/
theorem regular_scale {A : ℕ} (hA : 1 ≤ A) {n : ℕ} (hn : 4 ≤ n) :
    (M (A * n) : ℝ) ≤ A * (C : ℝ) ^ A * M n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hAn : A * n ≤ 2 ^ A * n := Nat.mul_le_mul_right _ (le_trans (by omega) (le_two_pow_mul hA))
  have h1 := gM_mono hdiv (a := A * n) (b := 2 ^ A * n) (by positivity) hAn
  have h2 := gM_pow_two hdiv hreg hn A
  have h := h1.trans h2
  unfold gM at h
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  rw [div_le_iff₀ (by push_cast; positivity)] at h
  calc (M (A * n) : ℝ) ≤ (C : ℝ) ^ A * ((M n : ℝ) / n) * ((A * n : ℕ) : ℝ) := h
    _ = A * (C : ℝ) ^ A * M n := by push_cast; field_simp

include hdiv hreg in
/-- **The binary-splitting bound**: `(log p + 1) 𝖬(A p (log p + 1)) ≤ C' 𝖬(p) log² p` for `p ≥ 4`,
with `C' = 4A C^{2A+1}`. -/
theorem regular_cost {A : ℕ} (hA : 1 ≤ A) {p : ℕ} (hp : 4 ≤ p) :
    ((Nat.log 2 p + 1 : ℕ) : ℝ) * M (A * p * (Nat.log 2 p + 1)) ≤
      4 * A * (C : ℝ) ^ (2 * A + 1) * M p * (Nat.log 2 p : ℝ) ^ 2 := by
  set L := Nat.log 2 p
  have hL : 2 ≤ L := two_le_log hp
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpL : 4 ≤ p * L := le_trans hp (Nat.le_mul_of_pos_right _ (by omega))
  -- `A p (L+1) ≤ (2A) (p L)`, so `𝖬(A p (L+1)) ≤ 𝖬(2A · pL)`, by monotonicity of `g`
  have hle : A * p * (L + 1) ≤ (2 * A) * (p * L) := by
    calc A * p * (L + 1) ≤ A * p * (2 * L) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * A) * (p * L) := by ring
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hscale := regular_scale hdiv hreg (A := 2 * A) (by omega) hpL
  have hreg' : (M (p * L) : ℝ) ≤ C * M p * L := by exact_mod_cast hreg p hp
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ M p := Nat.cast_nonneg _
  -- `𝖬(A p (L+1)) ≤ (A p (L+1))/(2A p L) · 𝖬(2A p L) ≤ 𝖬(2A p L)`
  have hM1 : (M (A * p * (L + 1)) : ℝ) ≤ M ((2 * A) * (p * L)) := by
    exact_mod_cast M_mono hdiv (by positivity) hle
  have hCA : (C : ℝ) ^ (2 * A) * (C * M p * L) = (C : ℝ) ^ (2 * A + 1) * M p * L := by ring
  have hL1 : ((L + 1 : ℕ) : ℝ) ≤ 2 * L := by exact_mod_cast (by omega : L + 1 ≤ 2 * L)
  calc ((L + 1 : ℕ) : ℝ) * M (A * p * (L + 1))
      ≤ (2 * L) * ((2 * A : ℕ) * (C : ℝ) ^ (2 * A) * (C * M p * L)) := by
        refine mul_le_mul hL1 (hM1.trans (hscale.trans ?_)) (Nat.cast_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hreg' (by positivity)
    _ = 4 * A * (C : ℝ) ^ (2 * A + 1) * M p * (L : ℝ) ^ 2 := by push_cast; ring

end Regular

end ZetaF.AppA
