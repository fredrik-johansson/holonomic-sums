/-
# `∑_{k ≥ k₀} I_k(s)` and `∑_{m ≥ 1} J_m(s)` are entire

Locally uniformly in `s`: `|I_k(s)| ≤ e^{-(k²-k₀²)u₀} B` and `|J_m(s)| ≤ e^{-π²(m²-1)/u₀} B`.
-/
import ZetaF.Continuation.Entire
import ZetaF.Bounds.Truncation

open MeasureTheory Set Filter Finset
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

lemma rpow_le_add_of_near {u x x₀ : ℝ} (hu : 0 < u) (hx : |x - x₀| ≤ 1 / 2) :
    u ^ (x - 1) ≤ u ^ (x₀ - 3 / 2) + u ^ (x₀ - 1 / 2) := by
  have := abs_le.1 hx
  rcases le_or_gt u 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hu h (by linarith)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hu.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h.le (by linarith)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hu.le _))

lemma integrableOn_rpow_mul_exp_Ioi {κ u₀ : ℝ} (hκ : 0 < κ) (hu₀ : 0 < u₀) (y : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ y * rexp (-(κ * u))) (Ioi u₀) := by
  have h : IntegrableOn (fun u : ℝ => ‖(u : ℂ) ^ ((y : ℂ) + 1 - 1) * (rexp (-(κ * u)) : ℂ)‖)
    (Ioi u₀) := (integrableOn_upperLaplace hκ hu₀ ((y : ℂ) + 1)).norm
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu : 0 < u := lt_trans hu₀ hu
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

/-- On `ball s₀ 1`, `‖1/Γ((s+n)/2)‖` is bounded. -/
lemma exists_bound_inv_Gamma_ball (s₀ : ℂ) (n : ℕ) :
    ∃ G, ∀ s ∈ Metric.ball s₀ 1, ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ ≤ G := by
  obtain ⟨G, hG⟩ := (isCompact_closedBall s₀ 1).exists_bound_of_continuousOn
    ((Complex.differentiable_one_div_Gamma.comp (differentiable_half_shift n)).continuous.continuousOn)
  exact ⟨G, fun s hs => hG s (Metric.ball_subset_closedBall hs)⟩

lemma re_half_near {s s₀ : ℂ} (hs : s ∈ Metric.ball s₀ 1) (n : ℕ) :
    |((s + n) / 2).re - ((s₀ + n) / 2).re| ≤ 1 / 2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have := (Complex.abs_re_le_norm (s - s₀)).trans hs.le
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re, Complex.sub_re] at this ⊢
  rw [show (s.re + n) / 2 - (s₀.re + n) / 2 = (s.re - s₀.re) / 2 by ring, abs_div, abs_two]
  linarith

/-- Uniform bound for the `k`-terms near `s₀`. -/
theorem kTerm_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hRk : R < k₀)
    {u₀ : ℝ} (hu₀ : 0 < u₀) (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ k : ℕ, k₀ ≤ k →
      ‖kTerm (kernel a s) u₀ k‖ ≤ rexp (-((k : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) * B := by
  have hk₀0 : (0 : ℝ) < k₀ := lt_of_le_of_lt hR hRk
  have hk₀1 : (1 : ℝ) ≤ k₀ := by
    have : 0 < k₀ := by exact_mod_cast hk₀0
    exact_mod_cast this
  have hκ₀ : 0 < (k₀ : ℝ) ^ 2 := by positivity
  obtain ⟨N, b, hb, hbn⟩ := kSeries_local_bound ha hR hRk hk₀1 hu₀ s₀
  have hsmall : ∀ n, ∃ G, ∀ s ∈ Metric.ball s₀ 1, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
      ∫ u in Ioi u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) * (rexp (-((k₀ : ℝ) ^ 2 * u)) : ℂ)‖ ≤ G := by
    intro n
    obtain ⟨G, hG⟩ := exists_bound_inv_Gamma_ball s₀ n
    set x₀ := ((s₀ + n) / 2).re
    set K := ∫ u in Ioi u₀, (u ^ (x₀ - 3 / 2) + u ^ (x₀ - 1 / 2)) * rexp (-((k₀ : ℝ) ^ 2 * u))
    refine ⟨‖a n‖ * G * K, fun s hs => ?_⟩
    apply mul_le_mul (mul_le_mul_of_nonneg_left (hG s hs) (norm_nonneg _)) _
      (integral_nonneg fun _ => norm_nonneg _) (by
        have := (norm_nonneg _).trans (hG s hs); positivity)
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · simp_rw [add_mul]
      exact (integrableOn_rpow_mul_exp_Ioi hκ₀ hu₀ _).add (integrableOn_rpow_mul_exp_Ioi hκ₀ hu₀ _)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu : 0 < u := lt_trans hu₀ hu
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      simp only [Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_right (rpow_le_add_of_near hu (re_half_near hs n))
        (Real.exp_pos _).le
  choose G hG using hsmall
  set g : ℕ → ℝ := fun n => if n < N then G n else b n
  have hg : Summable g := by
    have h1 : Summable fun n : ℕ => if n < N then G n - b n else 0 :=
      summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
        simp only [Finset.mem_range] at hn; simp [hn]
    refine (hb.add h1).congr fun n => ?_
    simp only [g]; split_ifs <;> ring
  refine ⟨∑' n, g n, fun s hs k hk => ?_⟩
  have hk' : R < (k : ℝ) := lt_of_lt_of_le hRk (by exact_mod_cast hk)
  have hk1 : (1 : ℝ) ≤ k := hk₀1.trans (by exact_mod_cast hk)
  have hsum := hasSum_kSeries ha hR hk' hk1 hu₀ s
  have hκ : 0 < (k : ℝ) ^ 2 := by positivity
  set E := rexp (-((k : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀)
  unfold kTerm
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖kSeriesTerm a ((k : ℝ) ^ 2) u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
      ∫ u in Ioi u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) * (rexp (-((k₀ : ℝ) ^ 2 * u)) : ℂ)‖) := by
    unfold kSeriesTerm upperLaplace
    rw [norm_mul, norm_mul, mul_left_comm, ← integral_const_mul]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by positivity)
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((integrableOn_upperLaplace hκ₀ hu₀ _).norm.const_mul E) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    dsimp only
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have := exp_sq_le (k := (k : ℝ)) (k₀ := (k₀ : ℝ)) (by exact_mod_cast hk) (Nat.cast_nonneg _)
      (le_of_lt hu)
    have e1 : rexp (-(((k : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀)) = E := by simp only [E, neg_mul]
    rw [e1] at this
    linarith
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs

/-- **`∑_{k ≥ k₀} I_k(s)` is entire.** -/
theorem differentiable_sum_kTerm (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hRk : R < k₀)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Differentiable ℂ fun s => ∑' k : ℕ, kTerm (kernel a s) u₀ (k + k₀) := by
  have hT : ∀ k : ℕ, Differentiable ℂ fun s => kTerm (kernel a s) u₀ (k + k₀) := by
    intro k
    have hlt : R < ((k + k₀ : ℕ) : ℝ) :=
      lt_of_lt_of_le hRk (Nat.cast_le.2 (Nat.le_add_left k₀ k))
    exact kTermEntire a R hR ha u₀ hu₀ (k + k₀) hlt
  refine differentiable_tsum_of_local_bound hT fun s₀ => ?_
  obtain ⟨B, hB⟩ := kTerm_local_bound ha hR hRk hu₀ s₀
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hB s₀ (Metric.mem_ball_self one_pos) k₀ le_rfl)
    simpa using this
  refine ⟨0, fun k => B * (rexp (-((k₀ : ℝ) ^ 2 - (k₀ : ℝ) ^ 2) * u₀) * rexp (-u₀) ^ k),
    ?_, fun k _ s hs => ?_⟩
  · exact ((tsum_exp_neg_sq_shift_le hu₀ k₀ _).summable).mul_left B
  · refine (hB s hs (k + k₀) (Nat.le_add_left _ _)).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (exp_shift_le hu₀ k₀ k _) hB0

lemma integrableOn_rpow_mul_dual_Ioc {c u₀ : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (y : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ y * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)))) (Ioc 0 u₀) := by
  have h : IntegrableOn (fun u : ℝ => ‖(u : ℂ) ^ ((y : ℂ) + 1 - 1) *
      ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖) (Ioc 0 u₀) :=
    (integrableOn_lowerDual hc hu₀ ((y : ℂ) + 1)).norm
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioc
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)]
  simp

/-- Uniform bound for the dual terms near `s₀`. -/
theorem dualTerm_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ m : ℕ, 1 ≤ m →
      ‖dualTerm (kernel a s) u₀ m‖ ≤ rexp (-((m : ℝ) ^ 2 - 1) * (π ^ 2 / u₀)) * B := by
  have hc₁ : (0 : ℝ) < π ^ 2 := by positivity
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc₁ u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  have hsmall : ∀ n, ∃ G, ∀ s ∈ Metric.ball s₀ 1, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
      ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 / u)) : ℝ) : ℂ)‖ ≤ G := by
    intro n
    obtain ⟨G, hG⟩ := exists_bound_inv_Gamma_ball s₀ n
    set x₀ := ((s₀ + n) / 2).re
    set K := ∫ u in Ioc 0 u₀, (u ^ (x₀ - 3 / 2) + u ^ (x₀ - 1 / 2)) *
      (u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 / u)))
    refine ⟨‖a n‖ * G * K, fun s hs => ?_⟩
    apply mul_le_mul (mul_le_mul_of_nonneg_left (hG s hs) (norm_nonneg _)) _
      (integral_nonneg fun _ => norm_nonneg _) (by
        have := (norm_nonneg _).trans (hG s hs); positivity)
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · simp_rw [add_mul]
      exact (integrableOn_rpow_mul_dual_Ioc hc₁ hu₀ _).add
        (integrableOn_rpow_mul_dual_Ioc hc₁ hu₀ _)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      dsimp only
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)]
      simp only [Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_right (rpow_le_add_of_near hu.1 (re_half_near hs n))
        (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)
  choose G hG using hsmall
  set g : ℕ → ℝ := fun n => if n < N then G n else b n
  have hg : Summable g := by
    have h1 : Summable fun n : ℕ => if n < N then G n - b n else 0 :=
      summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
        simp only [Finset.mem_range] at hn; simp [hn]
    refine (hb.add h1).congr fun n => ?_
    simp only [g]; split_ifs <;> ring
  refine ⟨∑' n, g n, fun s hs m hm => ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : 0 < π ^ 2 * (m : ℝ) ^ 2 := by positivity
  have hsum := hasSum_dSeries ha hR hc hu₀ s
  set E := rexp (-((m : ℝ) ^ 2 - 1) * (π ^ 2 / u₀))
  unfold dualTerm
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖dSeriesTerm a (π ^ 2 * (m : ℝ) ^ 2) u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 / u)) : ℝ) : ℂ)‖) := by
    unfold dSeriesTerm lowerDual
    rw [norm_mul, norm_mul, mul_left_comm, ← integral_const_mul]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by positivity)
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((integrableOn_lowerDual hc₁ hu₀ _).norm.const_mul E) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    dsimp only
    have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hr (Real.exp_pos _).le),
      Real.norm_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
    have hexp : rexp (-(π ^ 2 * (m : ℝ) ^ 2 / u)) ≤ E * rexp (-(π ^ 2 / u)) := by
      simp only [E]
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : π ^ 2 * ((m : ℝ) ^ 2 - 1) / u₀ ≤ π ^ 2 * ((m : ℝ) ^ 2 - 1) / u :=
        div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg π) (by nlinarith)) hu.1 hu.2
      have e : π ^ 2 * (m : ℝ) ^ 2 / u = π ^ 2 * ((m : ℝ) ^ 2 - 1) / u + π ^ 2 / u := by ring
      rw [e]
      have e2 : -((m : ℝ) ^ 2 - 1) * (π ^ 2 / u₀) = -(π ^ 2 * ((m : ℝ) ^ 2 - 1) / u₀) := by ring
      rw [e2]; linarith
    set P := ‖(u : ℂ) ^ ((s + n) / 2 - 1)‖
    have hP : 0 ≤ P := norm_nonneg _
    calc P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 * (m : ℝ) ^ 2 / u)))
        = (u ^ (-(1 / 2 : ℝ)) * P) * rexp (-(π ^ 2 * (m : ℝ) ^ 2 / u)) := by ring
      _ ≤ (u ^ (-(1 / 2 : ℝ)) * P) * (E * rexp (-(π ^ 2 / u))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hr hP)
      _ = E * (P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(π ^ 2 / u)))) := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs

/-- **`∑_{m ≥ 1} J_m(s)` is entire.** -/
theorem differentiable_sum_dualTerm (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Differentiable ℂ fun s => ∑' m : ℕ, dualTerm (kernel a s) u₀ (m + 1) := by
  have hT : ∀ m : ℕ, Differentiable ℂ fun s => dualTerm (kernel a s) u₀ (m + 1) :=
    fun m => dualTermEntire a R hR ha u₀ hu₀ (m + 1) (Nat.succ_pos m)
  refine differentiable_tsum_of_local_bound hT fun s₀ => ?_
  obtain ⟨B, hB⟩ := dualTerm_local_bound ha hR hu₀ s₀
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hB s₀ (Metric.mem_ball_self one_pos) 1 le_rfl)
    simpa using this
  have hc : 0 < π ^ 2 / u₀ := by positivity
  refine ⟨0, fun m => B * (rexp (-(((1 : ℕ) : ℝ) ^ 2 - 1) * (π ^ 2 / u₀)) *
    rexp (-(π ^ 2 / u₀)) ^ m), ?_, fun m _ s hs => ?_⟩
  · exact ((tsum_exp_neg_sq_shift_le hc 1 _).summable).mul_left B
  · have := hB s hs (m + 1) (Nat.le_add_left _ _)
    refine this.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    have := exp_shift_le hc 1 m 1
    simpa using this

end ZetaF
