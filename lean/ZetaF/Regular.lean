/-
# Functions analytic and regular at infinity; the zeta functions `ζ_F` and relatives

Paper: Definition 2.1 (`def:regular`), Definition 2.2 (`def:functions`), Lemma 2.3 (`lem:reduction`).

## Design

The paper defines `F ∈ 𝓡` via an operator `L` for which `∞` is an ordinary or regular singular point;
by Frobenius's method every solution then has an expansion (eq. (3))
`F(x) = ∑_{σ ∈ Σ} ∑_{j ≤ J} x^{-σ} (log x)^j f_{σ,j}(1/x)`.
Mathlib has no Frobenius theory, so we take the *expansion* as the primary datum
(`FrobeniusData`), and require each `f_{σ,j}` to be annihilated by an operator satisfying condition (H)
(`ThetaOp.IsFuchsian`).  This is exactly the form of the data that the paper uses from Appendix A.2 on;
the equivalence with the operator-based definition is Frobenius's theorem plus the monodromy argument of
Appendix A.2, recorded (unproved) as `FrobeniusEquivalence` in `ZetaF/Open.lean`.

A *sequence* in the class is one that eventually agrees with such an expansion.  The paper also asks the
values for `k₁ ≤ k < k₀` to come from analytic continuation; these finitely many values do not affect
any analytic statement about `ζ_F` (they contribute an entire Dirichlet polynomial), so we allow them to
be arbitrary.
-/
import ZetaF.Holonomic.ThetaOperator

open Complex Finset Filter LSeries

namespace ZetaF

/-- Geometric growth `‖a n‖ ≤ C R^n` of a coefficient sequence. -/
def GeomBounded (a : ℕ → ℂ) (R : ℝ) : Prop := ∃ C, ∀ n, ‖a n‖ ≤ C * R ^ n

/-- The function `x ↦ f(1/x) = ∑ a_n x^{-n}` attached to a coefficient sequence. -/
noncomputable def evalInv (a : ℕ → ℂ) (x : ℂ) : ℂ := ∑' n, a n * x⁻¹ ^ n

/-- A coefficient sequence is *Fuchsian-holonomic* (over the subfield `K`) if it is eventually
annihilated by a θ-operator with coefficients in `K` satisfying condition (H).  For `f = ∑ a_n x^n`
this says that `f` is holonomic with an ordinary or regular singular point at `0`, i.e. that
`x ↦ f(1/x)` is holonomic and regular at infinity. -/
def IsFuchsianHolonomic (K : Subfield ℂ) (a : ℕ → ℂ) : Prop :=
  ∃ L : ThetaOp ℂ, L.IsFuchsian ∧ L.AnnihilatesEventually a ∧
    ∀ j i, (L.coeff j).coeff i ∈ K

/-- The algebraic numbers, as a subfield of `ℂ`. -/
noncomputable abbrev algebraicNumbers : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

/-- **Analytic at infinity, with data** (the setting (4) of the paper):
`F(x) = f(1/x)`, `f(x) = ∑ a_n x^n`, `|a_n| ≤ C R^n`. -/
structure AnalyticAtInftyData where
  /-- Taylor coefficients of `f`. -/
  a : ℕ → ℂ
  /-- Growth rate; the expansion converges for `x > R`. -/
  R : ℝ
  R_nonneg : 0 ≤ R
  bound : GeomBounded a R

/-- Frobenius-type expansion at infinity (eq. (3) of the paper):
`F(x) = ∑_{σ ∈ Σ} ∑_{j ≤ J} x^{-σ} (log x)^j f_{σ,j}(1/x)`. -/
structure FrobeniusData where
  /-- The exponents `Σ`. -/
  exps : Finset ℂ
  /-- Maximal power of the logarithm. -/
  J : ℕ
  /-- Coefficients of the power series `f_{σ,j}`. -/
  f : ℂ → ℕ → ℕ → ℂ
  /-- Common growth rate. -/
  R : ℝ
  R_nonneg : 0 ≤ R
  bound : ∀ σ j, GeomBounded (f σ j) R
  /-- The exponents are pairwise incongruent modulo `ℤ`. -/
  incongruent : ∀ σ ∈ exps, ∀ τ ∈ exps, σ ≠ τ → ∀ m : ℤ, σ - τ ≠ m

namespace FrobeniusData

/-- Value of the expansion at a point `x` (used for `x > R`). -/
noncomputable def eval (D : FrobeniusData) (x : ℂ) : ℂ :=
  ∑ σ ∈ D.exps, ∑ j ∈ range (D.J + 1), x ^ (-σ) * Complex.log x ^ j * evalInv (D.f σ j) x

/-- The data are *regular*: every `f_{σ,j}` satisfies condition (H), over the subfield `K`, and the
exponents lie in `K`. -/
def IsRegularOver (D : FrobeniusData) (K : Subfield ℂ) : Prop :=
  (∀ σ ∈ D.exps, σ ∈ K) ∧ ∀ σ ∈ D.exps, ∀ j ≤ D.J, IsFuchsianHolonomic K (D.f σ j)

/-- The data have algebraic coefficients (in `K`). -/
def HasCoeffsIn (D : FrobeniusData) (K : Subfield ℂ) : Prop :=
  ∀ σ ∈ D.exps, ∀ j ≤ D.J, ∀ n, D.f σ j n ∈ K

end FrobeniusData

/-- A sequence is **analytic** (Definition 2.1(1), sequence version): it eventually agrees with
`k ↦ f(1/k)` for an `f` with geometrically bounded coefficients, beyond the radius of convergence. -/
def IsAnalyticSeq (F : ℕ → ℂ) : Prop :=
  ∃ D : AnalyticAtInftyData, ∃ k₀ : ℕ, D.R < k₀ ∧ ∀ k ≥ k₀, F k = evalInv D.a k

/-- A sequence is in the **regular class `𝓡`** (Definition 2.1(2)), with operator data over `K`. -/
def IsRegularSeqOver (K : Subfield ℂ) (F : ℕ → ℂ) : Prop :=
  ∃ D : FrobeniusData, D.IsRegularOver K ∧ ∃ k₀ : ℕ, D.R < k₀ ∧ ∀ k ≥ k₀, F k = D.eval k

/-- The class `𝓡` of regular sequences. -/
def RegClass : Set (ℕ → ℂ) := {F | IsRegularSeqOver ⊤ F}

/-- The class `𝓡_{Q̄}`: regular sequences whose operators, exponents and expansion coefficients are
algebraic. -/
def RegClassQbar : Set (ℕ → ℂ) :=
  {F | ∃ D : FrobeniusData, D.IsRegularOver algebraicNumbers ∧ D.HasCoeffsIn algebraicNumbers ∧
    ∃ k₀ : ℕ, D.R < k₀ ∧ ∀ k ≥ k₀, F k = D.eval k}

lemma RegClassQbar_subset : RegClassQbar ⊆ RegClass := by
  rintro F ⟨D, ⟨hσ, hD⟩, -, k₀, hk₀, hF⟩
  refine ⟨D, ⟨fun σ _ => Subfield.mem_top σ, fun σ hσ' j hj => ?_⟩, k₀, hk₀, hF⟩
  obtain ⟨L, h1, h2, -⟩ := hD σ hσ' j hj
  exact ⟨L, h1, h2, fun _ _ => Subfield.mem_top _⟩

/-! ### The functions attached to `F` (Definition 2.2) -/

/-- The zeta function `ζ_F(s) = ∑_{k ≥ 1} F(k) k^{-s}` (as a series; meaningful where it converges). -/
noncomputable def zetaF (F : ℕ → ℂ) (s : ℂ) : ℂ := LSeries F s

/-- The twisted zeta function `L_F(s, χ) = ∑ χ(k) F(k) k^{-s}`. -/
noncomputable def twistedZetaF (F χ : ℕ → ℂ) (s : ℂ) : ℂ := LSeries (fun k => χ k * F k) s

/-- The polylogarithm `Li_F(s, z) = ∑ F(k) z^k k^{-s}`. -/
noncomputable def polylogF (F : ℕ → ℂ) (s z : ℂ) : ℂ := LSeries (fun k => F k * z ^ k) s

/-- The Lerch transcendent `Φ_F(z, s, a) = ∑_{k ≥ 0} F(k) z^k (k+a)^{-s}`. -/
noncomputable def lerchF (F : ℕ → ℂ) (z s : ℂ) (a : ℝ) : ℂ :=
  ∑' k : ℕ, F k * z ^ k * ((k : ℂ) + a) ^ (-s)

/-- The damped zeta function `Λ_F(s; τ, r) = ∑ e^{-τ k^r} F(k) k^{-s}`. -/
noncomputable def dampedZetaF (F : ℕ → ℂ) (s : ℂ) (τ r : ℝ) : ℂ :=
  LSeries (fun k => (Real.exp (-(τ * (k : ℝ) ^ r)) : ℂ) * F k) s

/-- The tail of a sequence from index `k₀` on. -/
def tail (k₀ : ℕ) (F : ℕ → ℂ) (k : ℕ) : ℂ := if k₀ ≤ k then F k else 0

/-- `ζ_F^{≥ k₀}(s)`. -/
noncomputable def zetaTail (F : ℕ → ℂ) (k₀ : ℕ) : ℂ → ℂ := LSeries (tail k₀ F)

/-! ### Lemma 2.3 (reduction to the analytic case) -/

lemma evalInv_bounded {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R) {k₀ : ℝ}
    (hk₀ : R < k₀) : ∃ M, ∀ x : ℝ, k₀ ≤ x → ‖evalInv a x‖ ≤ M := by
  obtain ⟨C, hC⟩ := ha
  have hk₀pos : 0 < k₀ := lt_of_le_of_lt hR hk₀
  set q := R / k₀ with hq
  have hq0 : 0 ≤ q := div_nonneg hR hk₀pos.le
  have hq1 : q < 1 := (div_lt_one hk₀pos).2 hk₀
  refine ⟨C * (1 - q)⁻¹, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le hk₀pos hx
  have hterm : ∀ n, ‖a n * ((x : ℂ)⁻¹) ^ n‖ ≤ C * q ^ n := by
    intro n
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hxpos.le]
    calc ‖a n‖ * (x⁻¹) ^ n ≤ C * R ^ n * (x⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right (hC n) (by positivity)
      _ = C * (R / x) ^ n := by rw [div_eq_mul_inv, mul_pow, mul_assoc]
      _ ≤ C * q ^ n := by
          have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC 0)
          apply mul_le_mul_of_nonneg_left _ hC0
          apply pow_le_pow_left₀ (div_nonneg hR hxpos.le)
          exact div_le_div_of_nonneg_left hR hk₀pos hx
  have hsum : Summable fun n => C * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left C
  calc ‖evalInv a x‖ ≤ ∑' n, C * q ^ n :=
        tsum_of_norm_bounded hsum.hasSum hterm
    _ = C * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

lemma logMul_iterate_apply (g : ℕ → ℂ) (j k : ℕ) :
    (logMul^[j] g) k = Complex.log k ^ j * g k := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simp only [logMul]
    rw [ih]; ring

/-- A tail of a bounded sequence has abscissa of absolute convergence at most `1`. -/
lemma abscissa_tail_le_one {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R) {k₀ : ℕ}
    (hk₀ : R < k₀) : abscissaOfAbsConv (tail k₀ fun k => evalInv a k) ≤ 1 := by
  obtain ⟨M, hM⟩ := evalInv_bounded hR ha hk₀
  have := LSeries.abscissaOfAbsConv_le_of_le_const (f := tail k₀ fun k => evalInv a k)
    ⟨max M 0, fun n _ => ?_⟩
  · exact this
  unfold tail
  split_ifs with h
  · exact le_trans (hM n (by exact_mod_cast h)) (le_max_left _ _)
  · simp

/-- Shifting `s` by `σ` multiplies the coefficients by `k^{-σ}`. -/
lemma term_cpow_mul (h : ℕ → ℂ) (σ s : ℂ) (k : ℕ) :
    term (fun k => (k : ℂ) ^ (-σ) * h k) s k = term h (s + σ) k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
    rw [term_of_ne_zero hk, term_of_ne_zero hk, cpow_add _ _ hk', cpow_neg]
    have : (k : ℂ) ^ σ ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hk')
    have : (k : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hk')
    field_simp

lemma LSeries_cpow_mul (h : ℕ → ℂ) (σ s : ℂ) :
    LSeries (fun k => (k : ℂ) ^ (-σ) * h k) s = LSeries h (s + σ) := by
  have : term (fun k => (k : ℂ) ^ (-σ) * h k) s = term h (s + σ) := funext (term_cpow_mul h σ s)
  rw [LSeries, LSeries, this]

lemma LSeriesSummable_cpow_mul {h : ℕ → ℂ} {σ s : ℂ} (hh : LSeriesSummable h (s + σ)) :
    LSeriesSummable (fun k => (k : ℂ) ^ (-σ) * h k) s := by
  have : term (fun k => (k : ℂ) ^ (-σ) * h k) s = term h (s + σ) := funext (term_cpow_mul h σ s)
  rw [LSeriesSummable, this]; exact hh

/-- **Lemma 2.3.**  For `Re s` large (`Re(s+σ) > 1` for every exponent),
`ζ_F^{≥k₀}(s) = ∑_{σ,j} (-∂_s)^j ζ_{F_{σ,j}}^{≥k₀}(s+σ)`, where `F_{σ,j}(x) = f_{σ,j}(1/x)`. -/
theorem zetaTail_eq_sum_iteratedDeriv (D : FrobeniusData) {F : ℕ → ℂ} {k₀ : ℕ} (hk₀ : D.R < k₀)
    (hF : ∀ k ≥ k₀, F k = D.eval k) {s : ℂ} (hs : ∀ σ ∈ D.exps, 1 < (s + σ).re) :
    zetaTail F k₀ s = ∑ σ ∈ D.exps, ∑ j ∈ range (D.J + 1),
      (-1) ^ j * iteratedDeriv j (zetaTail (fun k => evalInv (D.f σ j) k) k₀) (s + σ) := by
  set g : ℂ → ℕ → ℕ → ℂ := fun σ j => tail k₀ fun k => evalInv (D.f σ j) k with hg
  have habs : ∀ σ ∈ D.exps, ∀ j, abscissaOfAbsConv (g σ j) < (s + σ).re := by
    intro σ hσ j
    exact lt_of_le_of_lt (by exact_mod_cast abscissa_tail_le_one D.R_nonneg (D.bound σ j) hk₀)
      (by exact_mod_cast hs σ hσ)
  have hsum : ∀ σ ∈ D.exps, ∀ j,
      LSeriesSummable (fun k => (k : ℂ) ^ (-σ) * (logMul^[j] (g σ j)) k) s := by
    intro σ hσ j
    apply LSeriesSummable_cpow_mul
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.abscissaOfAbsConv_logPowMul]
    exact habs σ hσ j
  have h1 : ∀ σ ∈ D.exps, ∀ j,
      (-1) ^ j * iteratedDeriv j (zetaTail (fun k => evalInv (D.f σ j) k) k₀) (s + σ)
      = LSeries (fun k => (k : ℂ) ^ (-σ) * (logMul^[j] (g σ j)) k) s := by
    intro σ hσ j
    unfold zetaTail
    rw [LSeries_iteratedDeriv j (habs σ hσ j), ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul]
    rw [LSeries_cpow_mul]
  rw [sum_congr rfl fun σ hσ => sum_congr rfl fun j _ => h1 σ hσ j]
  rw [sum_congr rfl fun σ hσ => (LSeries_sum fun j _ => hsum σ hσ j).symm]
  rw [← LSeries_sum fun σ hσ => LSeriesSummable.sum fun j _ => hsum σ hσ j]
  unfold zetaTail
  apply LSeries_congr
  intro k _
  simp only [Finset.sum_apply, logMul_iterate_apply, hg, tail]
  split_ifs with hk
  · rw [hF k hk, FrobeniusData.eval]
    exact sum_congr rfl fun σ _ => sum_congr rfl fun j _ => by ring
  · simp

end ZetaF
