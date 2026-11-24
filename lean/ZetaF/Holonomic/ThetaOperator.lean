/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Differential operators in θ-normal form

Following §3.2 of the paper, a linear differential operator with polynomial coefficients is written
in terms of the Euler operator `θ = x d/dx` as `∑_{j=0}^r x^j q_j(θ)`.  We store such an operator as a
polynomial in `x` whose coefficients `q_j` are polynomials (in `θ`): `ThetaOp K = K[X][X]`.

Acting on a power series `∑ a_m x^m` the monomial `x^j q(θ)` gives `∑ q(m) a_m x^{m+j}`, so the
coefficient of `x^n` in `L f` is `∑_j q_j(n-j) a_{n-j}` (`ThetaOp.applySeq`).  Condition (H) of the paper
(the operator is regular singular or ordinary at `x = 0`, by Fuchs's criterion) is
`deg q_0 ≥ deg q_j` for all `j` (`ThetaOp.IsFuchsian`).
-/
import ZetaF.Deps

open Polynomial Finset Filter

namespace ZetaF

/-- A linear differential operator in θ-normal form `∑_j x^j q_j(θ)`, stored as the polynomial in `x`
with coefficients `q_j ∈ K[θ]`. -/
abbrev ThetaOp (K : Type*) [CommRing K] := Polynomial (Polynomial K)

namespace ThetaOp

variable {K : Type*} [CommRing K]

/-- The coefficient of `x^n` in `L (∑ a_m x^m)`, namely `∑_{j ≤ n} q_j(n-j) a_{n-j}`. -/
def applySeq (L : ThetaOp K) (a : ℕ → K) (n : ℕ) : K :=
  ∑ j ∈ range (n + 1), (L.coeff j).eval ((n - j : ℕ) : K) * a (n - j)

/-- The action of a θ-operator on formal power series. -/
noncomputable def apply (L : ThetaOp K) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk (L.applySeq fun n => PowerSeries.coeff n f)

/-- Condition (H) of the paper: `q_0 ≠ 0` and `deg q_j ≤ deg q_0` for all `j`.  For an operator with
polynomial coefficients this is Fuchs's criterion for `x = 0` to be an ordinary or regular singular
point. -/
def IsFuchsian (L : ThetaOp K) : Prop :=
  L.coeff 0 ≠ 0 ∧ ∀ j, (L.coeff j).natDegree ≤ (L.coeff 0).natDegree

/-- `L` annihilates the coefficient sequence `a` up to finitely many coefficients, i.e. `L f` is a
polynomial.  This is the form "`∑_j q_j(n-j)a_{n-j} = 0` for large `n`" used in the paper. -/
def AnnihilatesEventually (L : ThetaOp K) (a : ℕ → K) : Prop :=
  ∀ᶠ n in atTop, L.applySeq a n = 0

/-- `L` annihilates the coefficient sequence `a` exactly. -/
def Annihilates (L : ThetaOp K) (a : ℕ → K) : Prop :=
  ∀ n, L.applySeq a n = 0

lemma Annihilates.eventually {L : ThetaOp K} {a : ℕ → K} (h : L.Annihilates a) :
    L.AnnihilatesEventually a :=
  Eventually.of_forall h

@[simp] lemma coeff_apply (L : ThetaOp K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (L.apply f) = L.applySeq (fun m => PowerSeries.coeff m f) n := by
  simp [apply]

lemma applySeq_add_op (L M : ThetaOp K) (a : ℕ → K) (n : ℕ) :
    (L + M).applySeq a n = L.applySeq a n + M.applySeq a n := by
  simp [applySeq, add_mul, sum_add_distrib]

lemma applySeq_add (L : ThetaOp K) (a b : ℕ → K) (n : ℕ) :
    L.applySeq (a + b) n = L.applySeq a n + L.applySeq b n := by
  simp [applySeq, mul_add, sum_add_distrib]

lemma applySeq_smul (L : ThetaOp K) (c : K) (a : ℕ → K) (n : ℕ) :
    L.applySeq (c • a) n = c * L.applySeq a n := by
  simp only [applySeq, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-! ### The Euler operator on formal power series -/

/-- The Euler operator `θ = X · d/dX` on formal power series. -/
noncomputable def theta : Module.End K (PowerSeries K) :=
  (LinearMap.mulLeft K (PowerSeries.X : PowerSeries K)) ∘ₗ
    (PowerSeries.derivative (R := K)).toLinearMap

lemma coeff_theta (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (theta f) = (n : K) * PowerSeries.coeff n f := by
  rcases n with _ | n
  · simp [theta]
  · simp [theta, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    ring

/-- A polynomial in `θ` acts diagonally on coefficients: `q(θ) x^n = q(n) x^n`. -/
lemma coeff_aeval_theta (q : K[X]) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (Polynomial.aeval (theta (K := K)) q f) =
      q.eval (n : K) * PowerSeries.coeff n f := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial m c =>
    induction m generalizing c with
    | zero => simp
    | succ m ih =>
      have h1 : Polynomial.aeval (theta (K := K)) (monomial (m + 1) c) =
          theta * Polynomial.aeval (theta (K := K)) (monomial m c) := by
        simp only [Polynomial.aeval_monomial, pow_succ']
        rw [show (algebraMap K (Module.End K (PowerSeries K))) c * (theta * theta ^ m) =
          theta * ((algebraMap K (Module.End K (PowerSeries K))) c * theta ^ m) by
            rw [← mul_assoc, ← mul_assoc, Algebra.commutes]]
      rw [h1, mul_apply_eq_comp, coeff_theta, ih]
      simp [Polynomial.eval_monomial, pow_succ]
      ring

/-- The formal action `ThetaOp.apply` agrees with the operator `∑_j X^j q_j(θ)`. -/
theorem apply_eq_sum (L : ThetaOp K) (f : PowerSeries K) :
    L.apply f = ∑ j ∈ L.support,
      PowerSeries.X ^ j * Polynomial.aeval (theta (K := K)) (L.coeff j) f := by
  ext n
  rw [coeff_apply, map_sum]
  simp only [PowerSeries.coeff_X_pow_mul', coeff_aeval_theta, applySeq]
  rw [← sum_filter]
  symm
  apply sum_subset
  · intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    omega
  · intro j _ hj'
    simp only [mem_filter, mem_support_iff, not_and] at hj'
    by_cases hjn : j ≤ n
    · have : L.coeff j = 0 := by
        by_contra h; exact hj' h hjn
      simp [this]
    · simp_all

end ThetaOp

/-! ### P-recursive sequences -/

/-- A sequence is *P-recursive* (holonomic) if it eventually satisfies a linear recurrence
`∑_{i=0}^d c_i(n) a_{n+i} = 0` with polynomial coefficients and `c_d ≠ 0`. -/
def IsPRecursive {K : Type*} [CommRing K] (a : ℕ → K) : Prop :=
  ∃ (d : ℕ) (c : ℕ → K[X]), c d ≠ 0 ∧
    ∀ᶠ n in atTop, ∑ i ∈ range (d + 1), (c i).eval ((n : ℕ) : K) * a (n + i) = 0

/-- A sequence annihilated (eventually) by a θ-operator with `q_0 ≠ 0` is P-recursive. -/
theorem ThetaOp.isPRecursive_of_annihilates {K : Type*} [CommRing K] [IsDomain K]
    {L : ThetaOp K} {a : ℕ → K} (h0 : L.coeff 0 ≠ 0) (h : L.AnnihilatesEventually a) :
    IsPRecursive a := by
  set r := L.natDegree
  refine ⟨r, fun i => (L.coeff (r - i)).comp (X + C ((i : ℕ) : K)), ?_, ?_⟩
  · simp only [Nat.sub_self]
    intro hc
    apply h0
    have := congrArg (fun p => p.comp (X - C ((r : ℕ) : K))) hc
    simpa [Polynomial.comp_assoc] using this
  · obtain ⟨N, hN⟩ := eventually_atTop.1 h
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have h1 := hN (n + r) (by omega)
    unfold ThetaOp.applySeq at h1
    have h2 : ∑ j ∈ range (r + 1), (L.coeff j).eval ((n + r - j : ℕ) : K) * a (n + r - j) = 0 := by
      rw [← h1]
      apply sum_subset
      · intro j hj; simp only [mem_range] at hj ⊢; omega
      · intro j _ hj'
        simp only [mem_range, not_lt] at hj'
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt (show r < j by omega)]
    rw [← sum_range_reflect] at h2
    rw [← h2]
    apply sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    have e1 : r + 1 - 1 - i = r - i := by omega
    have e2 : n + r - (r - i) = n + i := by omega
    simp only [e1, e2, eval_comp, eval_add, eval_X, eval_C, Nat.cast_add]

end ZetaF
