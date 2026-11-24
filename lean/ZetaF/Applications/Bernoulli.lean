/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Bernoulli polynomials at rational points as congruence L-values (Corollary 5.5)

The paper evaluates `B_n(x)` at a rational point `x = b/f'` in `(0, 1]` through the identity
`B_n(x) = -n f'^{1-n} L_1(1-n, 1_{b+f'ℤ})`, where `L_1(s, Φ) = ∑_{m ≥ 1} Φ(m) m^{-s}` continued
meromorphically. In Mathlib the continued congruence L-function is `ZMod.LFunction`, which agrees
with the Dirichlet series for `Re s > 1` (`ZMod.LFunction_eq_LSeries`). This file proves the identity.
-/
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.ZMod

open Complex HurwitzZeta

namespace ZetaF.Bernoulli

/-- Indicator of a residue class `b + Nℤ`, as a function on `ZMod N`. -/
noncomputable def classInd {N : ℕ} (b : ZMod N) : ZMod N → ℂ := fun j => if j = b then 1 else 0

lemma LFunction_classInd {N : ℕ} [NeZero N] (b : ZMod N) (s : ℂ) :
    ZMod.LFunction (classInd b) s = (N : ℂ) ^ (-s) * hurwitzZeta (ZMod.toAddCircle b) s := by
  unfold ZMod.LFunction classInd
  congr 1
  rw [Finset.sum_eq_single b]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The continued congruence L-function of `1_{b+Nℤ}` is its Dirichlet series for `Re s > 1`. -/
lemma LFunction_classInd_eq_LSeries {N : ℕ} [NeZero N] (b : ZMod N) {s : ℂ} (hs : 1 < s.re) :
    ZMod.LFunction (classInd b) s = LSeries (fun m => classInd b (m : ZMod N)) s :=
  ZMod.LFunction_eq_LSeries _ hs

/-- **The Bernoulli identity behind Corollary 5.5.** For `1 ≤ b ≤ N` and `n ≥ 2`,
`B_n(b/N) = -n N^{1-n} L(1-n, 1_{b+Nℤ})`. -/
theorem bernoulli_eq_LFunction {N : ℕ} [NeZero N] {b : ℕ} (hb : b ≤ N) {n : ℕ} (hn : 2 ≤ n) :
    ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((b : ℂ) / N) =
      -n * (N : ℂ) ^ (1 - (n : ℂ)) * ZMod.LFunction (classInd (b : ZMod N)) (1 - n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : k ≠ 0 := by omega
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  have hx : ((b : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hN).2 (by exact_mod_cast hb)⟩
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h1 : (1 : ℂ) - ((k + 1 : ℕ) : ℂ) = -(k : ℂ) := by push_cast; ring
  rw [LFunction_classInd, ZMod.toAddCircle_natCast, h1, hurwitzZeta_neg_nat hk hx]
  have hpow : (N : ℂ) ^ (-(k : ℂ)) * (N : ℂ) ^ (-(-(k : ℂ))) = 1 := by
    rw [← cpow_add _ _ hNc]; simp
  have hcast : (((b : ℝ) / N : ℝ) : ℂ) = (b : ℂ) / N := by push_cast; rfl
  rw [hcast]
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  set B := ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval ((b : ℂ) / N)
  have : -((k + 1 : ℕ) : ℂ) * (N : ℂ) ^ (-(k : ℂ)) * ((N : ℂ) ^ (-(-(k : ℂ))) * (-1 / ((k : ℂ) + 1) * B))
      = ((k + 1 : ℂ) / (k + 1)) * ((N : ℂ) ^ (-(k : ℂ)) * (N : ℂ) ^ (-(-(k : ℂ)))) * B := by
    push_cast; ring
  rw [this, hpow, div_self hk1, one_mul, one_mul]

/-- The same identity with `x = b/N` written through `ZMod.val`, for any residue `b : ZMod N`
(so `x ∈ [0, 1)`). -/
theorem bernoulli_eq_LFunction_val {N : ℕ} [NeZero N] (b : ZMod N) {n : ℕ} (hn : 2 ≤ n) :
    ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((b.val : ℂ) / N) =
      -n * (N : ℂ) ^ (1 - (n : ℂ)) * ZMod.LFunction (classInd b) (1 - n) := by
  have := bernoulli_eq_LFunction (N := N) (b := b.val) (ZMod.val_lt b).le hn
  rwa [ZMod.natCast_zmod_val] at this

end ZetaF.Bernoulli
