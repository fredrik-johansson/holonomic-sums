/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Liouville's inequality (Appendix A, lemma L8)

For a nonzero element `x` of a field with an admissible family of absolute values (e.g. a number
field with its places), every archimedean absolute value satisfies `1/H(x) ≤ |x|_v ≤ H(x)`, where
`H = Height.mulHeight₁` is the multiplicative height (`|x|_v ≤ H(x)` is immediate from the definition,
and the lower bound follows from `H(x⁻¹) = H(x)`, which encodes the product formula).

In Appendix A this bounds the small divisors: the divisions by `a* + n`, `s₀ + σ + n` and the `δ` of
(G3) are by nonzero algebraic numbers of height `p^{O(1)}`, hence by numbers of size at least
`p^{-O(1)}` (`small_divisor`, with `H(x + y) ≤ 2^d H(x) H(y)`).
-/
import Mathlib.NumberTheory.Height.NumberField

open Height AdmissibleAbsValues

namespace ZetaF.AppA

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- `|x|_v ≤ H(x)` for an archimedean absolute value `v` of the family. -/
theorem abv_le_mulHeight₁ {v : AbsoluteValue K ℝ} (hv : v ∈ archAbsVal (K := K)) (x : K) :
    v x ≤ mulHeight₁ x := by
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hv
  rw [mulHeight₁_eq, ht, Multiset.map_cons, Multiset.prod_cons]
  have h1 : 1 ≤ (t.map fun w => max (w x) 1).prod :=
    Multiset.one_le_prod_map fun _ _ => le_max_right _ _
  have h2 : 1 ≤ ∏ᶠ w : nonarchAbsVal (K := K), max (w.val x) 1 :=
    one_le_finprod fun _ => le_max_right _ _
  have h3 : v x ≤ max (v x) 1 := le_max_left _ _
  have h4 : 0 ≤ max (v x) 1 := le_trans zero_le_one (le_max_right _ _)
  calc v x ≤ max (v x) 1 := h3
    _ ≤ max (v x) 1 * (t.map fun w => max (w x) 1).prod * ∏ᶠ w : nonarchAbsVal (K := K), max (w.val x) 1 := by
        have : max (v x) 1 ≤ max (v x) 1 * (t.map fun w => max (w x) 1).prod :=
          le_mul_of_one_le_right h4 h1
        exact this.trans (le_mul_of_one_le_right (by positivity) h2)

/-- **Liouville's inequality**: `1/H(x) ≤ |x|_v` for `x ≠ 0` and every archimedean `v`. -/
theorem inv_mulHeight₁_le_abv {x : K} (hx : x ≠ 0) {v : AbsoluteValue K ℝ}
    (hv : v ∈ archAbsVal (K := K)) : 1 / mulHeight₁ x ≤ v x := by
  have h := abv_le_mulHeight₁ hv x⁻¹
  rw [mulHeight₁_inv, map_inv₀] at h
  have hvx : 0 < v x := v.pos hx
  rw [div_le_iff₀ (mulHeight₁_pos x)]
  calc (1 : ℝ) = (v x)⁻¹ * v x := (inv_mul_cancel₀ hvx.ne').symm
    _ ≤ mulHeight₁ x * v x := mul_le_mul_of_nonneg_right h hvx.le
    _ = v x * mulHeight₁ x := mul_comm _ _

/-- **Small divisors**: if `x + y ≠ 0` then `|x + y|_v ≥ 1/(2^d H(x) H(y))`, `d` the total weight of the
archimedean places (`[K : ℚ]` for a number field). -/
theorem small_divisor {x y : K} (hxy : x + y ≠ 0) {v : AbsoluteValue K ℝ}
    (hv : v ∈ archAbsVal (K := K)) :
    1 / (2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y) ≤ v (x + y) := by
  refine le_trans ?_ (inv_mulHeight₁_le_abv hxy hv)
  exact one_div_le_one_div_of_le (mulHeight₁_pos _) (mulHeight₁_add_le x y)

/-- The number-field form, for an infinite place `w`. -/
theorem inv_mulHeight₁_le_infinitePlace {F : Type*} [Field F] [NumberField F] {x : F} (hx : x ≠ 0)
    (w : NumberField.InfinitePlace F) : 1 / mulHeight₁ x ≤ w x :=
  inv_mulHeight₁_le_abv hx (v := w.1) (by
    show w.1 ∈ NumberField.multisetInfinitePlace F
    rw [NumberField.mem_multisetInfinitePlace]; exact w.2)

end ZetaF.AppA
