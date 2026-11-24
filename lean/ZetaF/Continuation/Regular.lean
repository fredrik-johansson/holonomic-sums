/-
# Meromorphic continuation of `ζ_F` for a general regular `F` (Lemma 2.3 for all `s`)

For `F(x) = ∑_{σ,j} x^{-σ} (log x)^j f_{σ,j}(1/x)` (`k ≥ k₀`), Lemma 2.3 and the continuation of the
analytic case give a function
`Z(s) = ∑_{k<k₀} F(k) k^{-s} + ∑_{σ,j} (-∂_s)^j Z_{σ,j}(s+σ)`
holomorphic away from the points `s = 1 - σ - n`, equal to `ζ_F(s)` where the Dirichlet series converges.
This is the analytic content of Proposition 5.3 (poles only at `1 - σ - n`).
-/
import ZetaF.Continuation.Theorem

open MeasureTheory Set Filter Finset LSeries
open scoped Real Topology

namespace ZetaF

/-- The continuation of `ζ_F^{≥k₀}` for regular `F` (with `u₀ = 1`). -/
noncomputable def regularRHS (D : FrobeniusData) (k₀ : ℕ) (s : ℂ) : ℂ :=
  ∑ σ ∈ D.exps, ∑ j ∈ range (D.J + 1),
    (-1) ^ j * iteratedDeriv j (splitRHS (D.f σ j) k₀ 1) (s + σ)

/-- The complement of the possible poles `1 - σ - n`. -/
def regularDomain (D : FrobeniusData) : Set ℂ := {s | ∀ σ ∈ D.exps, ∀ n : ℕ, s + σ ≠ 1 - n}

theorem differentiableOn_regularRHS (D : FrobeniusData) {k₀ : ℕ} (hRk : D.R < k₀) :
    DifferentiableOn ℂ (regularRHS D k₀) (regularDomain D) := by
  unfold regularRHS
  refine DifferentiableOn.fun_sum fun σ hσ => DifferentiableOn.fun_sum fun j _ => ?_
  apply DifferentiableOn.const_mul
  have hA := (differentiableOn_splitRHS (D.bound σ j) D.R_nonneg hRk one_pos).analyticOnNhd
    isOpen_notPoles
  have hd : DifferentiableOn ℂ (iteratedDeriv j (splitRHS (D.f σ j) k₀ 1))
      {s : ℂ | ∀ n : ℕ, s ≠ 1 - n} := by
    rw [iteratedDeriv_eq_iterate]; exact (hA.iterated_deriv j).differentiableOn
  exact hd.comp (differentiableOn_id.add_const σ) fun s hs n => hs σ hσ n

/-- `ζ_F^{≥k₀}(s) = regularRHS(s)` where all `Re(s + σ) > 1`. -/
theorem zetaTail_eq_regularRHS (D : FrobeniusData) {F : ℕ → ℂ} {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : D.R < k₀) (hF : ∀ k ≥ k₀, F k = D.eval k) {s : ℂ}
    (hs : ∀ σ ∈ D.exps, 1 < (s + σ).re) : zetaTail F k₀ s = regularRHS D k₀ s := by
  rw [zetaTail_eq_sum_iteratedDeriv D hRk hF hs, regularRHS]
  refine sum_congr rfl fun σ hσ => sum_congr rfl fun j _ => ?_
  congr 1
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (hs σ hσ)] with z hz
  exact zetaTail_eq_splitRHS (F := fun k => evalInv (D.f σ j) k) (D.bound σ j) D.R_nonneg hk₀ hRk
    (fun _ _ => rfl) one_pos hz

lemma isOpen_regularDomain (D : FrobeniusData) : IsOpen (regularDomain D) := by
  have : regularDomain D = ⋂ σ ∈ D.exps, (fun s => s + σ) ⁻¹' {s : ℂ | ∀ n : ℕ, s ≠ 1 - n} := by
    ext s; simp [regularDomain]
  rw [this]
  exact isOpen_biInter_finset fun σ _ => isOpen_notPoles.preimage (continuous_id.add continuous_const)

/-- **Meromorphic continuation of `ζ_F` for regular `F`.**  If `F(k)` agrees for `k ≥ k₀ > R` with a
Frobenius expansion, then `ζ_F` extends holomorphically to `ℂ ∖ {1 - σ - n}`. -/
theorem zetaF_continuation (D : FrobeniusData) {F : ℕ → ℂ} {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : D.R < k₀) (hF : ∀ k ≥ k₀, F k = D.eval k) :
    ∃ Z : ℂ → ℂ, DifferentiableOn ℂ Z (regularDomain D) ∧
      ∀ s : ℂ, (∀ σ ∈ D.exps, 1 < (s + σ).re) → Z s = zetaF F s := by
  refine ⟨fun s => ∑ k ∈ Finset.Ico 1 k₀, F k * (k : ℂ) ^ (-s) + regularRHS D k₀ s, ?_, ?_⟩
  · refine DifferentiableOn.add ?_ (differentiableOn_regularRHS D hRk)
    refine (Differentiable.fun_sum fun k hk => ?_).differentiableOn
    have hk0 : (k : ℂ) ≠ 0 := by
      simp only [Finset.mem_Ico] at hk; exact_mod_cast (by omega : k ≠ 0)
    exact (differentiable_neg.const_cpow (Or.inl hk0)).const_mul _
  · intro s hs
    dsimp only
    rw [← zetaTail_eq_regularRHS D hk₀ hRk hF hs]
    -- summability of the tail
    have hsum : LSeriesSummable (tail k₀ F) s := by
      set g : ℂ → ℕ → ℕ → ℂ := fun σ j => tail k₀ fun k => evalInv (D.f σ j) k with hg
      have hparts : ∀ σ ∈ D.exps, ∀ j, LSeriesSummable
          (fun k => (k : ℂ) ^ (-σ) * (logMul^[j] (g σ j)) k) s := by
        intro σ hσ j
        apply LSeriesSummable_cpow_mul
        apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
        rw [LSeries.abscissaOfAbsConv_logPowMul]
        exact lt_of_le_of_lt (by exact_mod_cast abscissa_tail_le_one D.R_nonneg (D.bound σ j) hRk)
          (by exact_mod_cast hs σ hσ)
      have hS := LSeriesSummable.sum (S := D.exps) fun σ hσ =>
        LSeriesSummable.sum (S := range (D.J + 1)) fun j _ => hparts σ hσ j
      refine (LSeriesSummable_congr s fun {n} _ => ?_).2 hS
      simp only [Finset.sum_apply, logMul_iterate_apply, hg, tail]
      split_ifs with hn
      · rw [hF n hn, FrobeniusData.eval]
        exact sum_congr rfl fun σ _ => sum_congr rfl fun j _ => by ring
      · simp
    have hsumF : LSeriesSummable F s := by
      refine (LSeriesSummable_congr' s ?_).2 hsum
      filter_upwards [eventually_ge_atTop k₀] with n hn
      simp [tail, hn]
    unfold zetaF zetaTail LSeries
    rw [← hsumF.sum_add_tsum_nat_add k₀, ← hsum.sum_add_tsum_nat_add k₀]
    have h1 : ∑ i ∈ range k₀, term (tail k₀ F) s i = 0 := sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi; simp [term, tail, show ¬ k₀ ≤ i by omega]
    have h2 : ∀ i, term (tail k₀ F) s (i + k₀) = term F s (i + k₀) := fun i => by
      simp [term, tail]
    have h3 : ∑ i ∈ range k₀, term F s i = ∑ k ∈ Finset.Ico 1 k₀, F k * (k : ℂ) ^ (-s) := by
      rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hk₀]
      simp only [Finset.Ico_self, Nat.Ico_zero_eq_range, range_one, sum_singleton, term_zero,
        zero_add]
      refine sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Ico] at hk
      rw [term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
    rw [h1, zero_add, h3]
    simp only [h2]

end ZetaF
