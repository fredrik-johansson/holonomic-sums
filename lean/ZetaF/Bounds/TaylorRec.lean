/-
# The Taylor recurrence of the bit-burst step (Appendix A.1)

If `Y(c) ∈ ℂ^D` satisfies `c Y'(c) = (B₀ + c B₁) Y(c)`, its Taylor coefficients `Y_l` at `c₀` satisfy
`c₀ (l+1) Y_{l+1} = (B₀ + c₀ B₁ - l) Y_l + B₁ Y_{l-1}`.
We prove this (as an equivalence) for formal power series in `h = c - c₀`: the system reads
`(c₀ + h) dY/dh = (B₀ + (c₀ + h) B₁) Y`.
-/
import ZetaF.Deps

open PowerSeries Finset

namespace ZetaF

variable {D : ℕ}

/-- A constant matrix acting on a vector of power series. -/
noncomputable def matApply (B : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) :
    Fin D → PowerSeries ℂ :=
  fun i => ∑ j, C (B i j) * Y j

/-- The coefficient `Y_{l-1}`, with `Y_{-1} = 0`. -/
noncomputable def prevCoeff (n : ℕ) (f : PowerSeries ℂ) : ℂ := if n = 0 then 0 else coeff (n - 1) f

lemma coeff_X_mul' (n : ℕ) (f : PowerSeries ℂ) : coeff n (X * f) = prevCoeff n f := by
  cases n with
  | zero => simp [prevCoeff]
  | succ n => rw [coeff_succ_X_mul]; simp [prevCoeff]

lemma coeff_matApply (B : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) (i : Fin D)
    (n : ℕ) : coeff n (matApply B Y i) = ∑ j, B i j * coeff n (Y j) := by
  simp [matApply, map_sum, coeff_C_mul]

lemma prevCoeff_matApply (B : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) (i : Fin D)
    (n : ℕ) : prevCoeff n (matApply B Y i) = ∑ j, B i j * prevCoeff n (Y j) := by
  unfold prevCoeff
  split_ifs
  · simp
  · exact coeff_matApply B Y i (n - 1)

/-- **Taylor recurrence of `c Y' = (B₀ + c B₁) Y` at `c₀`.** -/
theorem taylor_rec_iff (c₀ : ℂ) (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ) (Y : Fin D → PowerSeries ℂ) :
    (∀ i, (C c₀ + X) * d⁄dX (Y i) = matApply B₀ Y i + (C c₀ + X) * matApply B₁ Y i) ↔
    ∀ n i, c₀ * (n + 1) * coeff (n + 1) (Y i) =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * coeff n (Y j) - n * coeff n (Y i) +
        ∑ j, B₁ i j * prevCoeff n (Y j) := by
  have key : ∀ i n, coeff n ((C c₀ + X) * d⁄dX (Y i)) =
      c₀ * (n + 1) * coeff (n + 1) (Y i) + n * coeff n (Y i) := by
    intro i n
    rw [add_mul, map_add, coeff_C_mul, coeff_X_mul', coeff_derivative]
    unfold prevCoeff
    split_ifs with h
    · subst h; simp
    · rw [coeff_derivative, Nat.sub_add_cancel (Nat.pos_of_ne_zero h),
        Nat.cast_sub (Nat.pos_of_ne_zero h)]
      push_cast; ring
  have key2 : ∀ i n, coeff n (matApply B₀ Y i + (C c₀ + X) * matApply B₁ Y i) =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * coeff n (Y j) + ∑ j, B₁ i j * prevCoeff n (Y j) := by
    intro i n
    rw [map_add, add_mul, map_add, coeff_C_mul, coeff_X_mul', coeff_matApply, coeff_matApply,
      prevCoeff_matApply, mul_sum, ← add_assoc, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun j _ => by ring
  constructor
  · intro h n i
    have := congrArg (coeff n) (h i)
    rw [key, key2] at this
    linear_combination this
  · intro h i
    ext n
    rw [key, key2, h n i]
    ring

end ZetaF
