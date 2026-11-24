/-
# Theorem 3.2 for all `s`: meromorphic continuation of `ζ_F^{≥k₀}`

`Z(s) = ∑_{k ≥ k₀} I_k(s) + √π ∑_{m ≥ 1} J_m(s) + M(s)`, with `I_k`, `J_m` entire and `M` given by its
series, is holomorphic on `ℂ ∖ {1, 0, -1, …}` and equals `ζ_F^{≥k₀}(s)` for `Re s > 1`.
-/
import ZetaF.Continuation.MainTermEq
import Mathlib.Analysis.Normed.Module.Connected
import ZetaF.IncompleteGamma

open MeasureTheory Set Filter Finset
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-- The right-hand side of Theorem 3.2, valid for all `s`. -/
noncomputable def splitRHS (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, kTerm (kernel a s) u₀ (k + k₀) + √π * ∑' m : ℕ, dualTerm (kernel a s) u₀ (m + 1) +
    ∑' n, mainSeriesTerm a u₀ k₀ n s

/-- **Theorem 3.2, analytic part.** The right-hand side is holomorphic away from `s = 1 - n`. -/
theorem differentiableOn_splitRHS (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hRk : R < k₀)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    DifferentiableOn ℂ (splitRHS a k₀ u₀) {s | ∀ n : ℕ, s ≠ 1 - n} :=
  (((differentiable_sum_kTerm ha hR hRk hu₀).differentiableOn).add
    (((differentiable_sum_dualTerm ha hR hu₀).const_mul _).differentiableOn)).add
    (differentiableOn_mainSeries ha hR hu₀ k₀)

/-- **Theorem 3.2, identity part.** For `Re s > 1` it equals `ζ_F^{≥k₀}(s)`, for every `u₀ > 0`. -/
theorem zetaTail_eq_splitRHS (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {s : ℂ} (hs : 1 < s.re) : zetaTail F k₀ s = splitRHS a k₀ u₀ s := by
  rw [zetaTail_split ha hR hk₀ hRk hF hs hu₀, splitRHS,
    (hasSum_mainSeries ha hR hu₀ k₀ hs).tsum_eq]

/-- **Meromorphic continuation of `ζ_F^{≥k₀}`** (`ZetaTailContinuation` in `ZetaF/Open.lean`). -/
theorem zetaTailContinuation : ZetaTailContinuation := by
  intro a R hR ha F k₀ hk₀ hRk hF
  exact ⟨splitRHS a k₀ 1, differentiableOn_splitRHS ha hR hRk one_pos,
    fun s hs => (zetaTail_eq_splitRHS ha hR hk₀ hRk hF one_pos hs).symm⟩

/-- The domain `ℂ ∖ {1, 0, -1, …}` is open. -/
lemma isOpen_notPoles : IsOpen {s : ℂ | ∀ n : ℕ, s ≠ 1 - n} := by
  rw [Metric.isOpen_iff]
  intro s hs
  obtain ⟨N, hN⟩ := exists_nat_gt (2 - s.re)
  have hV : IsOpen {z : ℂ | ∀ n ∈ Finset.range N, z ≠ 1 - n} := by
    simp only [setOf_forall]
    exact isOpen_biInter_finset fun n _ => isOpen_ne_fun continuous_id continuous_const
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV s fun n _ => hs n
  refine ⟨min ε 1, lt_min hε one_pos, fun z hz n => ?_⟩
  by_cases hn : n < N
  · exact hεV (Metric.ball_subset_ball (min_le_left _ _) hz) n (Finset.mem_range.2 hn)
  · intro h
    have hz1 : dist z s < 1 := lt_of_lt_of_le hz (min_le_right _ _)
    rw [dist_eq_norm] at hz1
    have hre := (Complex.abs_re_le_norm (z - s)).trans hz1.le
    have : z.re = 1 - n := by rw [h]; simp
    simp only [Complex.sub_re] at hre
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast not_lt.1 hn
    have := abs_le.1 hre
    linarith

/-- The domain `ℂ ∖ {1, 0, -1, …}` is connected. -/
lemma isConnected_notPoles : IsConnected {s : ℂ | ∀ n : ℕ, s ≠ 1 - n} := by
  have : {s : ℂ | ∀ n : ℕ, s ≠ 1 - n} = (Set.range fun n : ℕ => (1 : ℂ) - n)ᶜ := by
    ext z; simp [eq_comm]
  rw [this]
  exact Set.Countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) (Set.countable_range _)

/-- **The split point `u₀` is a free parameter**: the continued function does not depend on it. -/
theorem splitRHS_indep (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : R < k₀) {u₀ u₁ : ℝ} (hu₀ : 0 < u₀) (hu₁ : 0 < u₁) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ 1 - n) : splitRHS a k₀ u₀ s = splitRHS a k₀ u₁ s := by
  have h2 : (2 : ℂ) ∈ {s : ℂ | ∀ n : ℕ, s ≠ 1 - n} := fun n h => by
    have := congrArg Complex.re h; simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hev : splitRHS a k₀ u₀ =ᶠ[𝓝 2] splitRHS a k₀ u₁ := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [← zetaTail_eq_splitRHS (F := fun k => evalInv a k) ha hR hk₀ hRk (fun _ _ => rfl) hu₀ hz,
      zetaTail_eq_splitRHS (F := fun k => evalInv a k) ha hR hk₀ hRk (fun _ _ => rfl) hu₁ hz]
  exact ((differentiableOn_splitRHS ha hR hRk hu₀).analyticOnNhd isOpen_notPoles).eqOn_of_preconnected_of_eventuallyEq
    ((differentiableOn_splitRHS ha hR hRk hu₁).analyticOnNhd isOpen_notPoles)
    isConnected_notPoles.isPreconnected h2 hev hs

/-! ### The series form of the `k`-terms in the paper's notation -/

/-- `∫_{u₀}^∞ u^{w-1} e^{-κu} du = κ^{-w} Γ(w, κu₀)`. -/
lemma upperLaplace_eq_upperGamma {κ u₀ : ℝ} (hκ : 0 < κ) (hu₀ : 0 ≤ u₀) (w : ℂ) :
    upperLaplace κ u₀ w = (κ : ℂ) ^ (-w) * upperGamma w (κ * u₀) := by
  have hκ' : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
  unfold upperLaplace upperGamma
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => (t : ℂ) ^ (w - 1) * (rexp (-t) : ℂ)) u₀ hκ
  have e : ∀ u ∈ Ioi u₀, (u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ) =
      (κ : ℂ) ^ (1 - w) * (((κ * u : ℝ) : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)) := by
    intro u hu
    have hu0 : 0 ≤ u := hu₀.trans (le_of_lt hu)
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hκ.le hu0, ← mul_assoc, ← mul_assoc,
      ← Complex.cpow_add _ _ hκ', show 1 - w + (w - 1) = 0 by ring, Complex.cpow_zero, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, h, Complex.real_smul,
    Complex.ofReal_inv]
  rw [show (1 - w) = -w + 1 by ring, Complex.cpow_add _ _ hκ', Complex.cpow_one]
  field_simp

lemma sq_cpow_neg {k : ℝ} (hk : 0 < k) (w : ℂ) : ((k ^ 2 : ℝ) : ℂ) ^ (-w) = (k : ℂ) ^ (-2 * w) := by
  rw [show ((k ^ 2 : ℝ) : ℂ) = ((k ^ (2 : ℝ) : ℝ) : ℂ) by rw [Real.rpow_two],
    ← Complex.cpow_mul_ofReal_nonneg hk.le]
  push_cast; ring_nf

/-- **Theorem 3.2, series form of the `k`-terms**, for every `s ∈ ℂ`:
`I_k(s) = ∑_n a_n k^{-s-n} Q((s+n)/2, k² u₀)`. -/
theorem hasSum_kTerm_gammaQ (ha : GeomBounded a R) (hR : 0 ≤ R) {k : ℕ} (hk : R < k)
    {u₀ : ℝ} (hu₀ : 0 < u₀) (s : ℂ) :
    HasSum (fun n => a n * (k : ℂ) ^ (-(s + n)) * gammaQ ((s + n) / 2) ((k : ℝ) ^ 2 * u₀))
      (kTerm (kernel a s) u₀ k) := by
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt hR hk
  have hk1 : (1 : ℝ) ≤ k := by
    have : 0 < k := by exact_mod_cast hk0
    exact_mod_cast this
  convert hasSum_kSeries ha hR hk hk1 hu₀ s using 1
  · funext n
    unfold kSeriesTerm gammaQ
    rw [upperLaplace_eq_upperGamma (by positivity) hu₀.le, sq_cpow_neg hk0,
      show -2 * ((s + n) / 2) = -(s + n) by ring, Complex.ofReal_natCast]
    ring
  · rfl

end ZetaF
