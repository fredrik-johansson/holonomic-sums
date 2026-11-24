/- Proposal for Appendix A (see APPENDIX_A_PLAN.md): statements only, `sorry` bodies. Not part of the library. -/
import ZetaF.Bounds.TaylorRec
import ZetaF.Bounds.BinarySplitting
import ZetaF.Bounds.Truncation
import ZetaF.Splitting.Kernel
import ZetaF.GammaG1
import ZetaF.IncompleteGammaSeries
import ZetaF.Holonomic.DualMoments
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Height.NumberField

/-! Scratch: proposed statements for the Appendix A refactoring (all `sorry`). -/

open Finset Real

namespace ZetaF.AppA

/-! ### L1. Taylor step (bit-burst stage), explicit -/

/-- All solutions of the Taylor recurrence of `cY' = (B₀ + cB₁)Y` at `c₀` satisfy
`‖h^l Y_l‖ ≤ (2θ)^l ‖Y_0‖` as soon as `|h|·‖B₀+c₀B₁‖/|c₀|, |h|·‖B₁‖, |h|/|c₀| ≤ θ`. -/
theorem taylor_step_bound {D : ℕ} {c₀ h : ℂ} (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ)
    (Y : ℕ → Fin D → ℂ)
    (hrec : ∀ n i, c₀ * (n + 1) * Y (n + 1) i =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * Y n j - n * Y n i +
        ∑ j, B₁ i j * (if n = 0 then 0 else Y (n - 1) j))
    (hc₀ : c₀ ≠ 0) {θ : ℝ}
    (h0 : ‖h‖ * (∑ i, ∑ j, ‖B₀ i j + c₀ * B₁ i j‖) ≤ θ * ‖c₀‖)
    (h1 : ‖h‖ * (∑ i, ∑ j, ‖B₁ i j‖) ≤ θ) (h2 : ‖h‖ ≤ θ * ‖c₀‖) (l : ℕ) :
    ‖h ^ l • Y l‖ ≤ (2 * θ) ^ l * ‖Y 0‖ := by
  sorry

/-- Consequences for `θ < 1/2`: the stage value is `≤ ‖Y₀‖/(1-2θ)` (so the transition map has
norm `≤ 1/(1-2θ)`), and the tail after `L` terms is `≤ (2θ)^L ‖Y₀‖/(1-2θ)`. -/
theorem taylor_step_tail {D : ℕ} {c₀ h : ℂ} (B₀ B₁ : Matrix (Fin D) (Fin D) ℂ)
    (Y : ℕ → Fin D → ℂ)
    (hrec : ∀ n i, c₀ * (n + 1) * Y (n + 1) i =
      ∑ j, (B₀ i j + c₀ * B₁ i j) * Y n j - n * Y n i +
        ∑ j, B₁ i j * (if n = 0 then 0 else Y (n - 1) j))
    (hc₀ : c₀ ≠ 0) {θ : ℝ} (hθ : θ < 1 / 2)
    (h0 : ‖h‖ * (∑ i, ∑ j, ‖B₀ i j + c₀ * B₁ i j‖) ≤ θ * ‖c₀‖)
    (h1 : ‖h‖ * (∑ i, ∑ j, ‖B₁ i j‖) ≤ θ) (h2 : ‖h‖ ≤ θ * ‖c₀‖) (L : ℕ) :
    Summable (fun k => h ^ (L + k) • Y (L + k)) ∧
      ‖∑' k, h ^ (L + k) • Y (L + k)‖ ≤ (2 * θ) ^ L * ‖Y 0‖ / (1 - 2 * θ) := by
  sorry

/-! ### L2. Product trees in a monoid with a quasi-subadditive size -/

/-- Node `(j,i)` of an ordered product tree in a (noncommutative) monoid. -/
def nodeL {α : Type*} [Monoid α] (x : ℕ → α) (j i : ℕ) : α :=
  ((List.range' (i * 2 ^ j) (2 ^ j)).map x).prod

/-- Cost of the tree if multiplying elements of sizes `a`, `b` costs `M (a + b)`. -/
def treeCostL {α : Type*} [Monoid α] (size : α → ℕ) (M : ℕ → ℕ) (x : ℕ → α) (d : ℕ) : ℕ :=
  ∑ j ∈ range d, ∑ i ∈ range (2 ^ (d - 1 - j)),
    M (size (nodeL x j (2 * i)) + size (nodeL x j (2 * i + 1)))

theorem treeCostL_le {α : Type*} [Monoid α] (size : α → ℕ) (κ : ℕ)
    (hsize : ∀ a b, size (a * b) ≤ size a + size b + κ)
    {M : ℕ → ℕ} (hmono : Monotone M) (hsup : ∀ a b, M a + M b ≤ M (a + b))
    (x : ℕ → α) (d : ℕ) :
    treeCostL size M x d ≤ d * M (∑ k ∈ range (2 ^ d), size (x k) + κ * 2 ^ d) := by
  sorry

/-- Entry size of an integer matrix. -/
def matSize {D : ℕ} (A : Matrix (Fin D) (Fin D) ℤ) : ℕ :=
  univ.sup fun ij : Fin D × Fin D => Nat.size (A ij.1 ij.2).natAbs

theorem matSize_mul_le {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℤ) :
    matSize (A * B) ≤ matSize A + matSize B + Nat.size D := by
  sorry

/-! ### L3. Regularity of `M` -/

/-- From `M(n)/n` nondecreasing and `M(n log n) ≤ C M(n) log n`: `M(A n) ≤ C' M(n)`, hence
`(log p + 1) M(A p (log p + 1)) = O(M(p) log² p)`. -/
theorem regular_cost {M : ℕ → ℕ} (hdiv : ∀ a b, 0 < a → a ≤ b → M a * b ≤ M b * a)
    {C : ℕ} (hreg : ∀ n ≥ 4, M (n * Nat.log 2 n) ≤ C * M n * Nat.log 2 n) (A : ℕ) :
    ∃ C' : ℕ, ∀ p ≥ 4,
      (Nat.log 2 p + 1) * M (A * p * (Nat.log 2 p + 1)) ≤ C' * M p * (Nat.log 2 p) ^ 2 := by
  sorry

/-! ### L4. Uniform kernel bounds (App. A.9, "Truncation") -/

theorem norm_kernel_le_far {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ u : ℝ, u₀ ≤ u →
      ‖kernel a s u‖ ≤ Real.exp (A * S * Real.log S) * (1 + u) ^ 2 * Real.exp (R ^ 2 * u) := by
  sorry

theorem norm_kernel_le_near {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      ‖kernel a s u‖ ≤ Real.exp (A * S * Real.log S) * u ^ (-(S / 2) - 1) := by
  sorry

theorem norm_kTerm_le_uniform {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R) (ha : ∀ n, ‖a n‖ ≤ C * R ^ n)
    {u₀ : ℝ} (hu₀ : 0 < u₀) {k₀ : ℕ} (hk₀ : R < k₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ k : ℕ, k₀ ≤ k →
      ‖kTerm (kernel a s) u₀ k‖ ≤
        Real.exp (A * S * Real.log S) * Real.exp (-(((k : ℝ) ^ 2 - R ^ 2) * u₀)) := by
  sorry

theorem norm_dualTerm_le_uniform {a : ℕ → ℂ} {C R : ℝ} (hR : 0 < R)
    (ha : ∀ n, ‖a n‖ ≤ C * R ^ n) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ s : ℂ, ‖s‖ ≤ S → ∀ m : ℕ, 1 ≤ m →
      ‖dualTerm (kernel a s) u₀ m‖ ≤
        Real.exp (A * S * Real.log S) * Real.exp (-(π ^ 2 * (m : ℝ) ^ 2 / (2 * u₀))) := by
  sorry

/-! ### L5. Sums of `x^j/Γ(σ+j+1)` (k-term inner sums, incomplete gamma series) -/

theorem sum_pow_mul_norm_inv_Gamma_le :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ σ : ℂ, ‖σ‖ ≤ S → ∀ x : ℝ, 0 ≤ x →
      Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j : ℕ, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤
        Real.exp (A * S * Real.log S) * (1 + x) ^ S * Real.exp x := by
  sorry

/-- Incomplete gamma series, uniform version: every term, and the tail from `N ≥ 2y + 2S`,
is `≤ e^{A S log S} (1+y)^S 2^{-N}`. -/
theorem norm_gammaPTerm_tail_uniform :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ a : ℂ, ‖a‖ ≤ S → ∀ y : ℝ, 0 < y → ∀ N : ℕ,
      2 * y + 2 * S ≤ N →
      ‖∑' i : ℕ, gammaPTerm a y (i + N)‖ ≤
        Real.exp (A * S * Real.log S) * (1 + y) ^ S * (1 / 2) ^ N := by
  sorry

/-! ### L6. Starting values: `D_{a+n} = α_n D_a + β_n E` and the `α`-series -/

/-- `α_n = (-c)^n/(a+1)_n`. -/
noncomputable def alphaD (a : ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  (-(c : ℂ)) ^ n / ∏ i ∈ range n, (a + 1 + i)

theorem momentD_add_nat_eq {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (a : ℂ)
    (ha : ∀ i : ℕ, a + 1 + i ≠ 0) :
    ∃ β : ℕ → ℂ, ∀ n : ℕ, momentD u₀ c (a + n) =
      alphaD a c n * momentD u₀ c a + β n * (rexp (-(c / u₀)) : ℂ) := by
  sorry

theorem sum_pow_div_factorial_sq_le {x : ℝ} (hx : 0 ≤ x) :
    ∑' n : ℕ, x ^ n / ((n.factorial : ℝ) ^ 2) ≤ Real.exp (2 * √x) := by
  sorry

/-! ### L7. Exactness for Bernoulli numbers (App. A.10) -/

theorem den_bernoulli_eval (n b f : ℕ) (hf : 0 < f) :
    ∃ z : ℤ, ((f : ℚ) ^ n * (primorial (n + 1) : ℚ)) *
      (Polynomial.bernoulli n).eval ((b : ℚ) / f) = z := by
  sorry

theorem abs_bernoulli_eval_le (n : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(((Polynomial.bernoulli n).eval x : ℚ) : ℝ)| ≤ 4 * Real.exp 1 * n.factorial := by
  sorry

theorem rat_eq_of_approx {q : ℚ} {D : ℕ} (hD : 0 < D) (hq : ∃ z : ℤ, (D : ℚ) * q = z)
    {y : ℝ} (hy : |y - q| < 1 / (2 * D)) : q = (round ((D : ℝ) * y) : ℚ) / D := by
  sorry

/-! ### L8. Liouville's inequality with Mathlib's (relative) height -/

theorem inv_mulHeight₁_le_place {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (v : NumberField.InfinitePlace K) : 1 / Height.mulHeight₁ x ≤ v x := by
  sorry

/-! ### L9. Log-moments (App. A.8) -/

noncomputable def dualMomentLog (u₀ c : ℝ) (t : ℂ) (i : ℕ) (g : ℝ → ℂ) : ℂ :=
  dualMoment u₀ c t fun u => (Real.log u : ℂ) ^ i * g u

theorem dualMomentLog_ibp {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (t : ℂ) (i : ℕ)
    {g g' : ℝ → ℂ} (hg : ∀ u ∈ Set.Icc 0 u₀, HasDerivAt g (g' u) u)
    (hg' : ContinuousOn g' (Set.Icc 0 u₀)) :
    c * dualMomentLog u₀ c (t + 1) (i + 1) g =
      (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (1 - t) * (Real.log u₀ : ℂ) ^ (i + 1) * g u₀ -
        (1 - t) * dualMomentLog u₀ c t (i + 1) g -
        dualMomentLog u₀ c t (i + 1) (fun u => u * g' u) -
        (i + 1) * dualMomentLog u₀ c t i g := by
  sorry

end ZetaF.AppA
