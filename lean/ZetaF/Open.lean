/-
# Open items, stated precisely

Statements from the paper recorded as `Prop`s (no `sorry`, no axioms), so that their exact form is
fixed.  Status:
* `KTermEntire`, `DualTermEntire`: **proved** (`kTermEntire`, `dualTermEntire` in
  `ZetaF/Continuation/Entire.lean`).
* `ZetaTailContinuation`: **proved** (`zetaTailContinuation` in `ZetaF/Continuation/Theorem.lean`).
* `EvenPartFuchsian`, `OddPartFuchsian`: reduced to the single hypothesis `FuchsianAddClosed ⊤`
  (Fuchs's criterion for the LCLM) in `ZetaF/Holonomic/Parity.lean`.
-/
import ZetaF.Splitting.Kernel

namespace ZetaF

/-- First paragraph of the proof of Lemma 3.1: the even part `A₀` of an `f` satisfying (H) again
satisfies (H).  (The paper argues via the LCLM of `L` and `L(-x)` and Fuchs's criterion.) -/
def EvenPartFuchsian : Prop :=
  ∀ a : ℕ → ℂ, IsFuchsianHolonomic ⊤ a → IsFuchsianHolonomic ⊤ fun m => a (2 * m)

/-- First paragraph of the proof of Lemma 3.1, odd part `A₁`. -/
def OddPartFuchsian : Prop :=
  ∀ a : ℕ → ℂ, IsFuchsianHolonomic ⊤ a → IsFuchsianHolonomic ⊤ fun m => a (2 * m + 1)

/-- Theorem 3.2: the `k`-terms `I_k(s)` are entire functions of `s` (for `k > R`). -/
def KTermEntire : Prop :=
  ∀ (a : ℕ → ℂ) (R : ℝ), 0 ≤ R → GeomBounded a R → ∀ u₀ : ℝ, 0 < u₀ → ∀ k : ℕ, R < k →
    Differentiable ℂ fun s => kTerm (kernel a s) u₀ k

/-- Theorem 3.2: the dual terms `J_m(s)` are entire functions of `s`. -/
def DualTermEntire : Prop :=
  ∀ (a : ℕ → ℂ) (R : ℝ), 0 ≤ R → GeomBounded a R → ∀ u₀ : ℝ, 0 < u₀ → ∀ m : ℕ, 0 < m →
    Differentiable ℂ fun s => dualTerm (kernel a s) u₀ m

/-- Proposition 5.7 / meromorphic continuation: `ζ_F^{≥k₀}` extends meromorphically to `ℂ`, with at most
simple poles at `s = 1 - n`.  Here in the weak form: the right-hand side of the splitting is analytic on
`Re s > 1` and extends analytically to `ℂ` minus `{1 - n}`. -/
def ZetaTailContinuation : Prop :=
  ∀ (a : ℕ → ℂ) (R : ℝ), 0 ≤ R → GeomBounded a R → ∀ F : ℕ → ℂ, ∀ k₀ : ℕ, 1 ≤ k₀ → R < k₀ →
    (∀ k ≥ k₀, F k = evalInv a k) →
    ∃ Z : ℂ → ℂ, DifferentiableOn ℂ Z {s | ∀ n : ℕ, s ≠ 1 - n} ∧
      ∀ s : ℂ, 1 < s.re → Z s = zetaTail F k₀ s

end ZetaF
