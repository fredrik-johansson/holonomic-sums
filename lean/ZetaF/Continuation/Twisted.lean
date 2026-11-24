/-
# Continuation of the twisted splitting (Remark 3.7, "then by continuation")

The pieces of the twisted splitting are holomorphic in `s`:
* weighted sums of `k`-terms (`differentiable_sum_kTerm_weighted`);
* weighted sums of dual terms with arbitrary `λ > 0` (`differentiable_sum_dualTermGen`);
* the main terms, written through `M_k(s)` (Theorem 3.2) and `H(s) = ∫₀^{u₀} h_s`, both continued
  by their termwise series.
For even periodic `χ` this gives the continuation of `L_F^{≥k₀}(s, χ)` to `ℂ ∖ {1, 0, -1, …}`
(`zetaTail_char_continuation`).
-/
import ZetaF.Twisted.SplitOdd
import ZetaF.Continuation.Hurwitz

open MeasureTheory Set Filter Finset
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-! ### Weighted sums of `k`-terms -/

/-- `s ↦ ∑_{k ≥ k₀} w_k I_k(s + σ)` is entire for `|w_k| ≤ B(k+1)`. -/
theorem differentiable_sum_kTerm_weighted (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ}
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) {w : ℕ → ℂ} {B : ℝ}
    (hw : ∀ k, ‖w k‖ ≤ B * ((k : ℝ) + 1)) (σ : ℂ) :
    Differentiable ℂ fun s => ∑' k : ℕ, w (k + k₀) * kTerm (kernel a (s + σ)) u₀ (k + k₀) := by
  have hT : ∀ k : ℕ, Differentiable ℂ fun s => w (k + k₀) * kTerm (kernel a (s + σ)) u₀ (k + k₀) := by
    intro k
    have hlt : R < ((k + k₀ : ℕ) : ℝ) :=
      lt_of_lt_of_le hRk (Nat.cast_le.2 (Nat.le_add_left k₀ k))
    exact ((kTermEntire a R hR ha u₀ hu₀ (k + k₀) hlt).comp
      (differentiable_id.add_const σ)).const_mul _
  refine differentiable_tsum_of_local_bound hT fun s₀ => ?_
  obtain ⟨B₁, hB₁⟩ := kTerm_local_bound ha hR hRk hu₀ (s₀ + σ)
  have hB₁0 : 0 ≤ B₁ := by
    have := (norm_nonneg _).trans (hB₁ (s₀ + σ) (Metric.mem_ball_self one_pos) k₀ le_rfl)
    simpa using this
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hw 0); simpa using this
  have hr : ‖rexp (-u₀)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one 0 hr
  refine ⟨0, fun k => B * B₁ * ((k : ℝ) ^ 1 * rexp (-u₀) ^ k + (k₀ + 1) * ((k : ℝ) ^ 0 *
    rexp (-u₀) ^ k)), ((hs1.add (hs0.mul_left _)).mul_left _), fun k _ s hs => ?_⟩
  have hs' : s + σ ∈ Metric.ball (s₀ + σ) 1 := by
    rw [Metric.mem_ball, dist_add_right]; exact hs
  rw [norm_mul]
  have h1 := hB₁ (s + σ) hs' (k + k₀) (Nat.le_add_left _ _)
  have h2 := exp_shift_le hu₀ k₀ k ((k₀ : ℝ) ^ 2)
  rw [sub_self, neg_zero, zero_mul, Real.exp_zero, one_mul] at h2
  have hwk := hw (k + k₀)
  calc ‖w (k + k₀)‖ * ‖kTerm (kernel a (s + σ)) u₀ (k + k₀)‖
      ≤ (B * (((k + k₀ : ℕ) : ℝ) + 1)) * (rexp (-u₀) ^ k * B₁) := by
        refine mul_le_mul hwk (h1.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h2 hB₁0
    _ = _ := by push_cast; ring

/-! ### Dual terms with a general `λ` -/

lemma differentiable_dualTermGen (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 0 < m) :
    Differentiable ℂ fun s => dualTermGen (kernel a s) u₀ lam m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < lam * (m : ℝ) ^ 2 := by positivity
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  have e : (fun s => dualTermGen (kernel a s) u₀ lam m) =
      fun s => ∑' n, dSeriesTerm a (lam * (m : ℝ) ^ 2) u₀ n s :=
    funext fun s => ((hasSum_dSeries ha hR hc hu₀ s).tsum_eq).symm
  rw [e]
  refine differentiable_tsum_of_local_bound (fun n => differentiable_dSeriesTerm hc hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  refine ⟨N, b, hb, fun n hn s hs => ?_⟩
  refine le_trans ?_ (hbn n hn s hs)
  unfold dSeriesTerm lowerDual
  rw [norm_mul, norm_mul]
  gcongr
  exact norm_integral_le_integral_norm _

/-- Uniform bound for the dual terms near `s₀`. -/
theorem dualTermGen_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {lam : ℝ} (hlam : 0 < lam) (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ m : ℕ, 1 ≤ m →
      ‖dualTermGen (kernel a s) u₀ lam m‖ ≤ rexp (-((m : ℝ) ^ 2 - 1) * (lam / u₀)) * B := by
  have hc₁ : (0 : ℝ) < lam := hlam
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc₁ u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  have hsmall : ∀ n, ∃ G, ∀ s ∈ Metric.ball s₀ 1, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
      ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)) : ℝ) : ℂ)‖ ≤ G := by
    intro n
    obtain ⟨G, hG⟩ := exists_bound_inv_Gamma_ball s₀ n
    set x₀ := ((s₀ + n) / 2).re
    set K := ∫ u in Ioc 0 u₀, (u ^ (x₀ - 3 / 2) + u ^ (x₀ - 1 / 2)) *
      (u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)))
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
  have hc : 0 < lam * (m : ℝ) ^ 2 := by positivity
  have hsum := hasSum_dSeries ha hR hc hu₀ s
  set E := rexp (-((m : ℝ) ^ 2 - 1) * (lam / u₀))
  unfold dualTermGen
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖dSeriesTerm a (lam * (m : ℝ) ^ 2) u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)) : ℝ) : ℂ)‖) := by
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
    have hexp : rexp (-(lam * (m : ℝ) ^ 2 / u)) ≤ E * rexp (-(lam / u)) := by
      simp only [E]
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : lam * ((m : ℝ) ^ 2 - 1) / u₀ ≤ lam * ((m : ℝ) ^ 2 - 1) / u :=
        div_le_div_of_nonneg_left (mul_nonneg hlam.le (by nlinarith)) hu.1 hu.2
      have e : lam * (m : ℝ) ^ 2 / u = lam * ((m : ℝ) ^ 2 - 1) / u + lam / u := by ring
      rw [e]
      have e2 : -((m : ℝ) ^ 2 - 1) * (lam / u₀) = -(lam * ((m : ℝ) ^ 2 - 1) / u₀) := by ring
      rw [e2]; linarith
    set P := ‖(u : ℂ) ^ ((s + n) / 2 - 1)‖
    have hP : 0 ≤ P := norm_nonneg _
    calc P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(lam * (m : ℝ) ^ 2 / u)))
        = (u ^ (-(1 / 2 : ℝ)) * P) * rexp (-(lam * (m : ℝ) ^ 2 / u)) := by ring
      _ ≤ (u ^ (-(1 / 2 : ℝ)) * P) * (E * rexp (-(lam / u))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hr hP)
      _ = E * (P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)))) := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs


/-- `s ↦ ∑_{m ≥ 1} d_m J_m^λ(s)` is entire for `|d_m| ≤ B(m+1)`. -/
theorem differentiable_sum_dualTermGen (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ}
    (hu₀ : 0 < u₀) {lam : ℝ} (hlam : 0 < lam) {d : ℕ → ℂ} {B : ℝ}
    (hd : ∀ m, ‖d m‖ ≤ B * ((m : ℝ) + 1)) :
    Differentiable ℂ fun s => ∑' m : ℕ, d (m + 1) * dualTermGen (kernel a s) u₀ lam (m + 1) := by
  have hT : ∀ m : ℕ, Differentiable ℂ fun s => d (m + 1) * dualTermGen (kernel a s) u₀ lam (m + 1) :=
    fun m => (differentiable_dualTermGen ha hR hu₀ hlam (Nat.succ_pos m)).const_mul _
  refine differentiable_tsum_of_local_bound hT fun s₀ => ?_
  obtain ⟨B₁, hB₁⟩ := dualTermGen_local_bound ha hR hu₀ hlam s₀
  have hB₁0 : 0 ≤ B₁ := by
    have := (norm_nonneg _).trans (hB₁ s₀ (Metric.mem_ball_self one_pos) 1 le_rfl)
    simpa using this
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hd 0); simpa using this
  have hc : 0 < lam / u₀ := by positivity
  have hr : ‖rexp (-(lam / u₀))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one 0 hr
  refine ⟨0, fun m => B * B₁ * ((m : ℝ) ^ 1 * rexp (-(lam / u₀)) ^ m + 2 * ((m : ℝ) ^ 0 *
    rexp (-(lam / u₀)) ^ m)), ((hs1.add (hs0.mul_left _)).mul_left _), fun m _ s hs => ?_⟩
  rw [norm_mul]
  have h1 := hB₁ s hs (m + 1) (Nat.le_add_left _ _)
  have h2 := exp_shift_le hc 1 m 1
  simp only [Nat.cast_one, one_pow, sub_self, neg_zero, zero_mul, Real.exp_zero, one_mul] at h2
  have hdm := hd (m + 1)
  calc ‖d (m + 1)‖ * ‖dualTermGen (kernel a s) u₀ lam (m + 1)‖
      ≤ (B * (((m + 1 : ℕ) : ℝ) + 1)) * (rexp (-(lam / u₀)) ^ m * B₁) := by
        refine mul_le_mul hdm (h1.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h2 hB₁0
    _ = _ := by push_cast; ring

/-! ### `H(s) = ∫₀^{u₀} h_s` -/

/-- A term of the series for `H(s)`: `a_n u₀^{w}/Γ(w+1)`, `w = (s+n)/2`. -/
noncomputable def hSeriesTerm (a : ℕ → ℂ) (u₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  a n * ((u₀ : ℂ) ^ ((s + n) / 2) * (Complex.Gamma ((s + n) / 2 + 1))⁻¹)

lemma differentiable_hSeriesTerm {u₀ : ℝ} (hu₀ : 0 < u₀) (n : ℕ) :
    Differentiable ℂ (hSeriesTerm a u₀ n) := by
  have hu : (u₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu₀.ne'
  intro s
  have hw : DifferentiableAt ℂ (fun s : ℂ => (s + n) / 2) s := (differentiable_half_shift n) s
  have hΓ1 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma ((s + n) / 2 + 1))⁻¹) s :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp s (hw.add_const 1)
  exact ((hw.const_cpow (Or.inl hu)).mul hΓ1).const_mul _

lemma hSeries_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (s₀ : ℂ) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧ ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1,
      ‖hSeriesTerm a u₀ n s‖ ≤ b n := by
  obtain ⟨N, C, hC0, hN⟩ := local_gamma_control s₀
  obtain ⟨Ca, hCa⟩ := ha
  have hCa0 : 0 ≤ Ca := le_trans (norm_nonneg _) (by simpa using hCa 0)
  set l : ℝ := 1 / (4 * (R ^ 2 + 1)) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; nlinarith
  have hq : R * √l < 1 := by
    have h1 : (R * √l) ^ 2 < 1 := by
      rw [mul_pow, Real.sq_sqrt hl0.le, hl]
      rw [← mul_div_assoc, mul_one, div_lt_one (by positivity)]; nlinarith
    nlinarith [Real.sqrt_nonneg l, mul_nonneg hR (Real.sqrt_nonneg l)]
  refine ⟨N, fun n => Ca * C * rexp (u₀ / l) * l ^ ((s₀.re - 1) / 2) * (R * √l) ^ n, ?_,
    fun n hn s hs => ?_⟩
  · exact (summable_geometric_of_lt_one (mul_nonneg hR (Real.sqrt_nonneg _)) hq).mul_left _
  obtain ⟨h1, h2, -⟩ := hN n hn s hs
  obtain ⟨h1', -, h3'⟩ := hN (n + 2) (by omega) s hs
  set w := (s + n) / 2 with hw
  set x := w.re
  have ew : (s + ((n + 2 : ℕ) : ℂ)) / 2 = w + 1 := by rw [hw]; push_cast; ring
  rw [ew] at h3'
  have hx0 : 0 < x := by linarith
  have hG1 := Real.Gamma_pos_of_pos (show 0 < x + 1 by linarith)
  have hΓ1 : ‖(Complex.Gamma (w + 1))⁻¹‖ ≤ C / Real.Gamma (x + 1) := by
    rw [le_div_iff₀ hG1]; simpa using h3'
  have hE := rpow_div_Gamma_le hx0 hu₀.le hl0
  have hpow : l ^ x ≤ l ^ ((s₀.re - 1) / 2) * (√l) ^ n := by
    rw [← rpow_half_add_nat hl0]
    exact Real.rpow_le_rpow_of_exponent_ge hl0 hl1 (by linarith)
  unfold hSeriesTerm
  rw [← hw, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu₀]
  calc ‖a n‖ * (u₀ ^ x * ‖(Complex.Gamma (w + 1))⁻¹‖)
      ≤ (Ca * R ^ n) * (C * (u₀ ^ x / Real.Gamma (x + 1))) := by
        apply mul_le_mul (hCa n) _ (by positivity) (by positivity)
        calc u₀ ^ x * ‖(Complex.Gamma (w + 1))⁻¹‖ ≤ u₀ ^ x * (C / Real.Gamma (x + 1)) := by
              gcongr
          _ = _ := by ring
    _ ≤ (Ca * R ^ n) * (C * (rexp (u₀ / l) * (l ^ ((s₀.re - 1) / 2) * (√l) ^ n))) := by
        gcongr
        exact hE.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = _ := by simp only [mul_pow]; ring

/-- `s ↦ ∑_n a_n u₀^{(s+n)/2}/Γ((s+n)/2+1)` is entire. -/
theorem differentiable_hSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Differentiable ℂ fun s => ∑' n, hSeriesTerm a u₀ n s :=
  differentiable_tsum_of_local_bound (fun n => differentiable_hSeriesTerm hu₀ n)
    (hSeries_local_bound ha hR hu₀)

/-- `∫₀^{u₀} h_s = ∑_n a_n u₀^{(s+n)/2}/Γ((s+n)/2+1)` for `Re s > 0`. -/
theorem hasSum_hSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) {s : ℂ}
    (hs : 0 < s.re) :
    HasSum (fun n => hSeriesTerm a u₀ n s) (∫ u in Ioc 0 u₀, kernel a s u) := by
  obtain ⟨D, hD0, hD⟩ := exists_coeff_bound ha hs
  set σ := s.re
  have hr : ∀ n : ℕ, -1 < (σ + n) / 2 - 1 := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hrc : ∀ n : ℕ, -1 < ((s + n) / 2 - 1).re := fun n => by
    simpa [σ] using hr n
  have hint : ∀ n, IntegrableOn (kernelTerm a s n) (Ioc 0 u₀) := fun n => by
    have h1 : IntegrableOn (fun u : ℝ => a n * (Complex.Gamma ((s + n) / 2))⁻¹ *
        (u : ℂ) ^ ((s + n) / 2 - 1)) (Ioc 0 u₀) :=
      (integrableOn_Ioc_cpow hu₀ (hrc n)).const_mul _
    exact h1
  have hval : ∀ n, ∫ u in Ioc 0 u₀, kernelTerm a s n u = hSeriesTerm a u₀ n s := by
    intro n
    set w := (s + n) / 2 with hw
    have hw0 : 0 < w.re := by simp [hw]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have hwne : w ≠ 0 := fun h => by rw [h] at hw0; simp at hw0
    simp only [kernelTerm]
    rw [integral_const_mul, ← hw, integral_Ioc_cpow hu₀ (by simpa [hw] using hrc n),
      sub_add_cancel, hSeriesTerm, ← hw, ← mul_inv_Gamma_add_one w]
    field_simp
  have hsum : Summable fun n => ∫ u in Ioc 0 u₀, ‖kernelTerm a s n u‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_majCoeff_mul_pow (D := D) (σ := σ) (q := √u₀) hR hs
        (Real.sqrt_nonneg _)).mul_left (2 / σ * u₀ ^ (σ / 2)))
    have hrn := hr n
    calc ∫ u in Ioc 0 u₀, ‖kernelTerm a s n u‖
        ≤ ∫ u in Ioc 0 u₀, majCoeff D R σ n * u ^ ((σ + n) / 2 - 1) := by
          refine setIntegral_mono_on (hint n).norm (((intervalIntegrable_iff_integrableOn_Ioc_of_le
            hu₀.le).1 (intervalIntegral.intervalIntegrable_rpow' hrn)).const_mul _)
            measurableSet_Ioc fun u hu => norm_kernelTerm_le hD hu.1 n
      _ = majCoeff D R σ n * (u₀ ^ ((σ + n) / 2) / ((σ + n) / 2)) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hu₀.le,
            integral_rpow (Or.inl hrn), Real.zero_rpow (by linarith), sub_zero,
            show (σ + n) / 2 - 1 + 1 = (σ + n) / 2 by ring]
      _ ≤ 2 / σ * u₀ ^ (σ / 2) * (majCoeff D R σ n * √u₀ ^ n) := by
          rw [rpow_half_add_nat hu₀]
          have hm := majCoeff_nonneg hD0 hR hs n (D := D) (R := R)
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hp : 0 ≤ u₀ ^ (σ / 2) * √u₀ ^ n := by positivity
          have : u₀ ^ (σ / 2) * √u₀ ^ n / ((σ + n) / 2) ≤ 2 / σ * (u₀ ^ (σ / 2) * √u₀ ^ n) := by
            calc _ ≤ u₀ ^ (σ / 2) * √u₀ ^ n / (σ / 2) :=
                  div_le_div_of_nonneg_left hp (by positivity) (by linarith)
              _ = _ := by field_simp
          calc majCoeff D R σ n * (u₀ ^ (σ / 2) * √u₀ ^ n / ((σ + n) / 2))
              ≤ majCoeff D R σ n * (2 / σ * (u₀ ^ (σ / 2) * √u₀ ^ n)) :=
                mul_le_mul_of_nonneg_left this hm
            _ = _ := by ring
  have := hasSum_integral_of_summable_integral_norm hint hsum
  simp only [hval] at this
  convert this using 1
  rfl

/-! ### The general main term through `M_k` and `H` -/

lemma mainWeight_one (u : ℝ) (hu : 0 < u) :
    (mainWeight 1 u : ℂ) = ((√π / 2 : ℝ) : ℂ) * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) - 1 / 2 := by
  unfold mainWeight
  simp only [Ico_self, sum_empty, sub_zero]
  rw [Real.sqrt_div' _ hu.le, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  push_cast; ring

lemma mainWeight_sub_succ {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    mainWeight k u - mainWeight (k + 1) u = rexp (-((k : ℝ) ^ 2 * u)) := by
  unfold mainWeight
  rw [sum_Ico_succ_top hk]; ring

/-- For `Re s` large: `M^χ = (2α/√π) M_1 + (β + α/√π) H - ∑_{k<k₀} c_k (M_k - M_{k+1})`. -/
lemma mainTermGen_eq {h : ℝ → ℂ} {u₀ : ℝ} (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hn0 : IntegrableOn (fun u => ‖h u‖) (Ioc 0 u₀)) (c : ℕ → ℂ) (α β : ℂ) (k₀ : ℕ) :
    mainTermGen h u₀ c α β k₀ = 2 * α / (√π : ℂ) * mainTerm h u₀ 1 +
      (β + α / (√π : ℂ)) * (∫ u in Ioc 0 u₀, h u) -
      ∑ k ∈ Ico 1 k₀, c k * (mainTerm h u₀ k - mainTerm h u₀ (k + 1)) := by
  have hsπ : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hh : IntegrableOn h (Ioc 0 u₀) :=
    Integrable.mono' hn0 ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      (Eventually.of_forall fun _ => le_rfl)
  have hM : ∀ k : ℕ, IntegrableOn (fun u => (mainWeight k u : ℂ) * h u) (Ioc 0 u₀) := fun k =>
    have hg : IntegrableOn (fun u => (1 / 2 * √π * u ^ (-(1 / 2 : ℝ)) + ((k : ℝ) + 1)) * ‖h u‖)
        (Ioc 0 u₀) := by
      have h1 : IntegrableOn (fun u => 1 / 2 * √π * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) +
          ((k : ℝ) + 1) * ‖h u‖) (Ioc 0 u₀) :=
        (hnear.const_mul (1 / 2 * √π)).add (hn0.const_mul ((k : ℝ) + 1))
      exact h1.congr_fun (fun u _ => by ring) measurableSet_Ioc
    integrableOn_weight_mul_of_le hcont (continuousOn_mainWeight k) Ioc_subset_Ioi_self
      measurableSet_Ioc hg (fun u hu => abs_mainWeight_le hu.1)
  have hS : IntegrableOn (fun u => ∑ k ∈ Ico 1 k₀, c k * ((mainWeight k u : ℂ) * h u -
      (mainWeight (k + 1) u : ℂ) * h u)) (Ioc 0 u₀) :=
    integrable_finsetSum _ fun k _ => ((hM k).sub (hM (k + 1))).const_mul _
  have e1 : ∀ k : ℕ, c k * (mainTerm h u₀ k - mainTerm h u₀ (k + 1)) =
      ∫ u in Ioc 0 u₀, c k * ((mainWeight k u : ℂ) * h u - (mainWeight (k + 1) u : ℂ) * h u) := by
    intro k
    rw [integral_const_mul, integral_sub (hM k) (hM (k + 1))]; rfl
  have e2 : ∫ u in Ioc 0 u₀, (∑ k ∈ Ico 1 k₀, c k * ((mainWeight k u : ℂ) * h u -
      (mainWeight (k + 1) u : ℂ) * h u)) = ∑ k ∈ Ico 1 k₀, ∫ u in Ioc 0 u₀, c k *
        ((mainWeight k u : ℂ) * h u - (mainWeight (k + 1) u : ℂ) * h u) :=
    integral_finsetSum _ fun k _ => ((hM k).sub (hM (k + 1))).const_mul _
  have e3 : 2 * α / (√π : ℂ) * mainTerm h u₀ 1 + (β + α / (√π : ℂ)) * (∫ u in Ioc 0 u₀, h u) =
      ∫ u in Ioc 0 u₀, (2 * α / (√π : ℂ) * ((mainWeight 1 u : ℂ) * h u) +
        (β + α / (√π : ℂ)) * h u) := by
    rw [integral_add ((hM 1).const_mul _) (hh.const_mul _), integral_const_mul,
      integral_const_mul]; rfl
  have hA : IntegrableOn (fun u => 2 * α / (√π : ℂ) * ((mainWeight 1 u : ℂ) * h u) +
      (β + α / (√π : ℂ)) * h u) (Ioc 0 u₀) := ((hM 1).const_mul _).add (hh.const_mul _)
  have e4 : (∫ u in Ioc 0 u₀, (2 * α / (√π : ℂ) * ((mainWeight 1 u : ℂ) * h u) +
        (β + α / (√π : ℂ)) * h u)) - ∫ u in Ioc 0 u₀, (∑ k ∈ Ico 1 k₀, c k *
        ((mainWeight k u : ℂ) * h u - (mainWeight (k + 1) u : ℂ) * h u)) =
      ∫ u in Ioc 0 u₀, ((2 * α / (√π : ℂ) * ((mainWeight 1 u : ℂ) * h u) +
        (β + α / (√π : ℂ)) * h u) - ∑ k ∈ Ico 1 k₀, c k *
        ((mainWeight k u : ℂ) * h u - (mainWeight (k + 1) u : ℂ) * h u)) :=
    (integral_sub hA hS).symm
  simp_rw [e1]
  rw [← e2, e3, e4]
  unfold mainTermGen
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [mainWeightGen, mainWeight_one u hu.1]
  have hsub : ∀ k ∈ Finset.Ico 1 k₀, c k * ((mainWeight k u : ℂ) * h u - (mainWeight (k + 1) u : ℂ) * h u) =
      c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * h u := fun k hk => by
    rw [← sub_mul, ← Complex.ofReal_sub, mainWeight_sub_succ (Finset.mem_Ico.1 hk).1]; ring
  rw [sum_congr rfl hsub, ← sum_mul]
  generalize (∑ k ∈ Finset.Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) = S
  have hsπ' : (√π : ℂ) ≠ 0 := hsπ
  push_cast
  field_simp
  ring

/-- The continuation of the general main term `M^χ`. -/
noncomputable def twistMainCont (a : ℕ → ℂ) (u₀ : ℝ) (c : ℕ → ℂ) (α β : ℂ) (k₀ : ℕ) (s : ℂ) : ℂ :=
  2 * α / (√π : ℂ) * (∑' n, mainSeriesTerm a u₀ 1 n s) +
    (β + α / (√π : ℂ)) * (∑' n, hSeriesTerm a u₀ n s) -
    ∑ k ∈ Finset.Ico 1 k₀, c k * ((∑' n, mainSeriesTerm a u₀ k n s) -
      ∑' n, mainSeriesTerm a u₀ (k + 1) n s)

theorem differentiableOn_twistMainCont (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ}
    (hu₀ : 0 < u₀) (c : ℕ → ℂ) (α β : ℂ) (k₀ : ℕ) :
    DifferentiableOn ℂ (twistMainCont a u₀ c α β k₀) notPoles := by
  have hM : ∀ k, DifferentiableOn ℂ (fun s => ∑' n, mainSeriesTerm a u₀ k n s) notPoles :=
    fun k => differentiableOn_mainSeries ha hR hu₀ k
  unfold twistMainCont
  refine ((((hM 1).const_mul _).add
    ((differentiable_hSeries ha hR hu₀).differentiableOn.const_mul _)).sub ?_)
  exact DifferentiableOn.fun_sum fun k _ => ((hM k).sub (hM (k + 1))).const_mul _

lemma integrableOn_norm_kernel (ha : GeomBounded a R) (hR : 0 ≤ R) {s : ℂ} (hs : 0 < s.re)
    {u₀ : ℝ} (hu₀ : 0 < u₀) : IntegrableOn (fun u => ‖kernel a s u‖) (Ioc 0 u₀) := by
  have := integrableOn_rpow_neg_mul_norm_kernel ha hR hs (t := 0) (by linarith) hu₀
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioc
  simp

theorem twistMainCont_eq (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (c : ℕ → ℂ) (α β : ℂ) (k₀ : ℕ) {s : ℂ} (hs : 1 < s.re) :
    twistMainCont a u₀ c α β k₀ s = mainTermGen (kernel a s) u₀ c α β k₀ := by
  have hs0 : 0 < s.re := by linarith
  rw [mainTermGen_eq (continuousOn_kernel ha hR hs0)
    (integrableOn_rpow_neg_half_mul_norm_kernel ha hR hs hu₀)
    (integrableOn_norm_kernel ha hR hs0 hu₀), twistMainCont,
    (hasSum_hSeries ha hR hu₀ hs0).tsum_eq]
  simp only [fun k => (hasSum_mainSeries ha hR hu₀ k hs).tsum_eq]

/-! ### The continuation for even periodic weights -/

/-- The right-hand side of the even twisted splitting, continued to `ℂ ∖ {1, 0, -1, …}`. -/
noncomputable def twistedEvenRHS (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (q : ℕ) (χ : ℤ → ℂ) (s : ℂ) : ℂ :=
  (∑' k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * kTerm (kernel a s) u₀ (k + k₀)) +
    (∑' m : ℕ, charDual q χ (m + 1) * dualTermGen (kernel a s) u₀ (π ^ 2 / q ^ 2) (m + 1)) +
    twistMainCont a u₀ (fun k => χ k) (charAlpha q χ) (-(1 / 2) * χ 0) k₀ s

theorem differentiableOn_twistedEvenRHS (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ}
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ}
    (hper : Function.Periodic χ q) :
    DifferentiableOn ℂ (twistedEvenRHS a k₀ u₀ q χ) notPoles := by
  set Bχ := ∑ a ∈ range q, ‖χ a‖
  have hB0 : 0 ≤ Bχ := sum_nonneg fun _ _ => norm_nonneg _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hk := differentiable_sum_kTerm_weighted ha hR hRk hu₀ (w := fun k : ℕ => χ k) (B := Bχ)
    (fun k => (periodic_bound hq hper k).trans (le_mul_of_one_le_right hB0
      (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith))) 0
  simp only [add_zero] at hk
  have hd := differentiable_sum_dualTermGen ha hR hu₀ (lam := π ^ 2 / q ^ 2) (by positivity)
    (d := charDual q χ) (B := √π / q * Bχ) (fun m => by
      rw [charDual, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      refine (mul_le_mul_of_nonneg_left (gaussSum_norm_le χ m) (by positivity)).trans ?_
      exact le_mul_of_one_le_right (by positivity)
        (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith))
  exact ((hk.differentiableOn.add hd.differentiableOn).add
    (differentiableOn_twistMainCont ha hR hu₀ _ _ _ k₀))

theorem zetaTail_char_eq_twistedEvenRHS (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ}
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ}
    (hs : 1 < s.re) {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (heven : ∀ k, χ (-k) = χ k) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    zetaTail (fun k => χ k * F k) k₀ s = twistedEvenRHS a k₀ u₀ q χ s := by
  rw [zetaTail_split_char ha hR hk₀ hRk hF hs hq hper heven hu₀, twistedEvenRHS,
    twistMainCont_eq ha hR hu₀ _ _ _ k₀ hs]

/-- **Remark 3.7, continuation (even case)**: for an even `q`-periodic `χ`, the tail
`L_F^{≥k₀}(s, χ)` continues holomorphically to `ℂ ∖ {1, 0, -1, …}`, and the twisted splitting
holds there. -/
theorem zetaTail_char_continuation (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {q : ℕ} (hq : 0 < q)
    {χ : ℤ → ℂ} (hper : Function.Periodic χ q) (heven : ∀ k, χ (-k) = χ k) {u₀ : ℝ}
    (hu₀ : 0 < u₀) :
    DifferentiableOn ℂ (twistedEvenRHS a k₀ u₀ q χ) notPoles ∧
      ∀ s : ℂ, 1 < s.re → twistedEvenRHS a k₀ u₀ q χ s = zetaTail (fun k => χ k * F k) k₀ s :=
  ⟨differentiableOn_twistedEvenRHS ha hR hRk hu₀ hq hper, fun _ hs =>
    (zetaTail_char_eq_twistedEvenRHS ha hR hk₀ hRk hF hs hq hper heven hu₀).symm⟩

/-- The continued right-hand side does not depend on `u₀`. -/
theorem twistedEvenRHS_indep (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : R < k₀) {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (heven : ∀ k, χ (-k) = χ k) {u₀ u₁ : ℝ} (hu₀ : 0 < u₀) (hu₁ : 0 < u₁) :
    Set.EqOn (twistedEvenRHS a k₀ u₀ q χ) (twistedEvenRHS a k₀ u₁ q χ) notPoles := by
  have h2 : (2 : ℂ) ∈ notPoles := fun n h => by
    have := congrArg Complex.re h; simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hev : twistedEvenRHS a k₀ u₀ q χ =ᶠ[𝓝 2] twistedEvenRHS a k₀ u₁ q χ := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [← zetaTail_char_eq_twistedEvenRHS (F := fun k => evalInv a k) ha hR hk₀ hRk
        (fun _ _ => rfl) hz hq hper heven hu₀,
      zetaTail_char_eq_twistedEvenRHS (F := fun k => evalInv a k) ha hR hk₀ hRk
        (fun _ _ => rfl) hz hq hper heven hu₁]
  exact ((differentiableOn_twistedEvenRHS ha hR hRk hu₀ hq hper).analyticOnNhd
    isOpen_notPoles).eqOn_of_preconnected_of_eventuallyEq
    ((differentiableOn_twistedEvenRHS ha hR hRk hu₁ hq hper).analyticOnNhd isOpen_notPoles)
    isConnected_notPoles.isPreconnected h2 hev

/-! ### Residues -/

/-- If all terms but the `n`-th are holomorphic near `s₀`, the tail is locally dominated, and
`(s - s₀) T_n(s) → ρ`, then `(s - s₀) ∑_m T_m(s) → ρ`. -/
lemma tendsto_residue_tsum {T : ℕ → ℂ → ℂ} {s₀ : ℂ} {n N : ℕ} {r : ℝ} (hr : 0 < r)
    (hT : ∀ m, m ≠ n → DifferentiableOn ℂ (T m) (Metric.ball s₀ r)) {b : ℕ → ℝ}
    (hb : Summable b) (hbn : ∀ m ≥ N, ∀ s ∈ Metric.ball s₀ r, ‖T m s‖ ≤ b m) {ρ : ℂ}
    (hn : Tendsto (fun s => (s - s₀) * T n s) (𝓝[≠] s₀) (𝓝 ρ)) :
    Tendsto (fun s => (s - s₀) * ∑' m, T m s) (𝓝[≠] s₀) (𝓝 ρ) := by
  set T' : ℕ → ℂ → ℂ := fun m s => if m = n then 0 else T m s with hT'
  have hG : DifferentiableAt ℂ (fun s => ∑' m, T' m s) s₀ := by
    refine differentiableAt_tsum_of_local_bound (N := N) hr (fun m => ?_) hb (fun m hm s hs => ?_)
    · by_cases hmn : m = n
      · simp only [hT', hmn, ite_true]; exact differentiableOn_const _
      · simp only [hT', hmn, ite_false]; exact hT m hmn
    · by_cases hmn : m = n
      · have := hbn m hm s hs
        simp only [hT', hmn, ite_true, norm_zero] at this ⊢
        exact (norm_nonneg _).trans this
      · simp only [hT', hmn, ite_false]; exact hbn m hm s hs
  have hGlim : Tendsto (fun s => (s - s₀) * ∑' m, T' m s) (𝓝[≠] s₀) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℂ => (s - s₀) * ∑' m, T' m s) s₀ :=
      ((continuousAt_id.sub continuousAt_const).mul hG.continuousAt)
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have heq : ∀ᶠ s in 𝓝[≠] s₀, (s - s₀) * ∑' m, T m s =
      (s - s₀) * T n s + (s - s₀) * ∑' m, T' m s := by
    have hball : Metric.ball s₀ r ∈ 𝓝[≠] s₀ := nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hr)
    filter_upwards [hball] with s hs
    have hsum : Summable fun m => T m s := by
      refine Summable.of_norm_bounded_eventually hb ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop N] with m hm
      exact hbn m hm s hs
    rw [hsum.tsum_eq_add_tsum_ite n, mul_add]
  have := (hn.add hGlim).congr' (EventuallyEq.symm heq)
  rwa [add_zero] at this

/-- `M_k` has residue `a_n` at `s = 1 - n`, for every `k`. -/
theorem mainSeries_residue (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (k₀ n : ℕ) :
    Tendsto (fun s => (s - (1 - n)) * ∑' m, mainSeriesTerm a u₀ k₀ m s) (𝓝[≠] (1 - n))
      (𝓝 (a n)) := by
  set s₀ : ℂ := 1 - n with hs₀
  obtain ⟨N, b, hb, hbn⟩ := mainSeries_local_bound ha hR hu₀ k₀ s₀
  have hu : (u₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu₀.ne'
  refine tendsto_residue_tsum (T := fun m => mainSeriesTerm a u₀ k₀ m) (n := n) (r := 1 / 2)
    (N := N) (by norm_num) (fun m hmn s hs => ?_) hb
    (fun m hm s hs => hbn m hm s (Metric.ball_subset_ball (by norm_num) hs)) ?_
  · refine (differentiableAt_mainSeriesTerm hu₀ k₀ m ?_).differentiableWithinAt
    have hs' := mem_notPoles_of_near (n := n) hs
    intro h
    by_cases hsn : s = 1 - n
    · apply hmn
      have : (m : ℂ) = n := by rw [hsn] at h; linear_combination h
      exact_mod_cast this
    · exact hs' hsn m (by linear_combination h)
  · -- the `n`-th term
    set w : ℂ → ℂ := fun s => (s + n) / 2 with hw
    set P : ℂ → ℂ := fun s => a n * ((√π : ℂ) * (u₀ : ℂ) ^ (w s - 1 / 2) *
      (Complex.Gamma (w s))⁻¹ - (s - s₀) * ((u₀ : ℂ) ^ (w s) * (Complex.Gamma (w s + 1))⁻¹ / 2 +
      ∑ k ∈ Ico 1 k₀, ((k : ℂ) ^ (-2 * w s) - (Complex.Gamma (w s))⁻¹ *
        upperLaplace ((k : ℝ) ^ 2) u₀ (w s)))) with hP
    have hwd : Differentiable ℂ w := differentiable_half_shift n
    have hPc : ContinuousAt P s₀ := by
      have hΓ : Continuous fun s => (Complex.Gamma (w s))⁻¹ :=
        (Complex.differentiable_one_div_Gamma.comp hwd).continuous
      have hΓ1 : Continuous fun s => (Complex.Gamma (w s + 1))⁻¹ :=
        (Complex.differentiable_one_div_Gamma.comp (hwd.add_const 1)).continuous
      have hcp : ∀ g : ℂ → ℂ, Continuous g → Continuous fun s => (u₀ : ℂ) ^ (g s) :=
        fun g hg => hg.const_cpow (Or.inl hu)
      have hsum : Continuous fun s => ∑ k ∈ Ico 1 k₀, ((k : ℂ) ^ (-2 * w s) -
          (Complex.Gamma (w s))⁻¹ * upperLaplace ((k : ℝ) ^ 2) u₀ (w s)) := by
        refine continuous_finsetSum _ fun k hk => ?_
        have hk0 : (k : ℂ) ≠ 0 := by
          simp only [Finset.mem_Ico] at hk; exact_mod_cast (by omega : k ≠ 0)
        have hk' : 0 < (k : ℝ) ^ 2 := by
          simp only [Finset.mem_Ico] at hk
          have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          positivity
        exact ((continuous_const.mul hwd.continuous).const_cpow (Or.inl hk0)).sub
          (hΓ.mul ((differentiable_upperLaplace hk' hu₀).continuous.comp hwd.continuous))
      refine (Continuous.continuousAt ?_)
      exact continuous_const.mul (((continuous_const.mul (hcp _ (hwd.continuous.sub continuous_const))).mul
        hΓ).sub ((continuous_id.sub continuous_const).mul
          (((hcp _ hwd.continuous).mul hΓ1).div_const _ |>.add hsum)))
    have hP0 : P s₀ = a n := by
      have hws : w s₀ = 1 / 2 := by simp only [hw, hs₀]; ring
      simp only [hP, hws, sub_self, zero_mul, sub_zero, Complex.cpow_zero, mul_one,
        Complex.Gamma_one_half_eq]
      have hsπ : (π : ℂ) ^ (1 / 2 : ℂ) = (√π : ℂ) := by
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
      rw [hsπ, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'),
        mul_one]
    have hlim : Tendsto P (𝓝[≠] s₀) (𝓝 (a n)) := hP0 ▸ hPc.tendsto.mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : s + n - 1 ≠ 0 := fun h => hs (by
      rw [Set.mem_singleton_iff, hs₀]; linear_combination h)
    simp only [hP, mainSeriesTerm, hw, hs₀]
    field_simp
    ring

/-- **Residues of the even twisted `L`-function**: at `s = 1 - n` the continuation has residue
`a_n χ̂(0)/q`, i.e. `a_n` times the mean value of `χ`. -/
theorem twistedEvenRHS_residue (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hRk : R < k₀)
    {u₀ : ℝ} (hu₀ : 0 < u₀) {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (n : ℕ) :
    Tendsto (fun s => (s - (1 - n)) * twistedEvenRHS a k₀ u₀ q χ s) (𝓝[≠] (1 - n))
      (𝓝 (gaussSum q χ 0 / q * a n)) := by
  set s₀ : ℂ := 1 - n
  set Bχ := ∑ a ∈ range q, ‖χ a‖
  have hB0 : 0 ≤ Bχ := sum_nonneg fun _ _ => norm_nonneg _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hk := differentiable_sum_kTerm_weighted ha hR hRk hu₀ (w := fun k : ℕ => χ k) (B := Bχ)
    (fun k => (periodic_bound hq hper k).trans (le_mul_of_one_le_right hB0
      (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith))) 0
  simp only [add_zero] at hk
  have hd := differentiable_sum_dualTermGen ha hR hu₀ (lam := π ^ 2 / q ^ 2) (by positivity)
    (d := charDual q χ) (B := √π / q * Bχ) (fun m => by
      rw [charDual, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      refine (mul_le_mul_of_nonneg_left (gaussSum_norm_le χ m) (by positivity)).trans ?_
      exact le_mul_of_one_le_right (by positivity)
        (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith))
  have hzero : ∀ f : ℂ → ℂ, ContinuousAt f s₀ →
      Tendsto (fun s => (s - s₀) * f s) (𝓝[≠] s₀) (𝓝 0) := fun f hf => by
    have hc : ContinuousAt (fun s : ℂ => (s - s₀) * f s) s₀ :=
      (continuousAt_id.sub continuousAt_const).mul hf
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hM := fun k => mainSeries_residue ha hR hu₀ k n
  have hH := hzero _ (differentiable_hSeries ha hR hu₀ (a := a)).continuous.continuousAt
  set α := charAlpha q χ
  have hmain : Tendsto (fun s => (s - s₀) * twistMainCont a u₀ (fun k => χ k) α
      (-(1 / 2) * χ 0) k₀ s) (𝓝[≠] s₀) (𝓝 (2 * α / (√π : ℂ) * a n)) := by
    have h1 := (((hM 1).const_mul (2 * α / (√π : ℂ))).add (hH.const_mul
      (-(1 / 2) * χ 0 + α / (√π : ℂ)))).sub (tendsto_finsetSum (Finset.Ico 1 k₀)
        fun k _ => ((hM k).sub (hM (k + 1))).const_mul (χ k))
    simp only [sub_self, mul_zero, Finset.sum_const_zero, sub_zero, add_zero] at h1
    refine h1.congr fun s => ?_
    simp only [twistMainCont, mul_sub, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have hall := ((hzero _ (hk s₀).continuousAt).add (hzero _ (hd s₀).continuousAt)).add hmain
  rw [zero_add, zero_add] at hall
  have hval : 2 * α / (√π : ℂ) * a n = gaussSum q χ 0 / q * a n := by
    simp only [α, charAlpha]
    have hsπ : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    push_cast; field_simp
  rw [hval] at hall
  refine hall.congr fun s => ?_
  simp only [twistedEvenRHS]; ring

/-! ### Odd dual terms `Z_{3/2}[h_{s+1}](λm²)` -/

/-- A term of the series for `Z_{3/2}[h_{s+1}](c)`. -/
noncomputable def dSeriesTermOdd (a : ℕ → ℂ) (c u₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹ * lowerDual c u₀ ((s + 1 + n) / 2 - 1)

lemma differentiable_dSeriesTermOdd {c u₀ : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (n : ℕ) :
    Differentiable ℂ (dSeriesTermOdd a c u₀ n) := by
  have hw : Differentiable ℂ fun s : ℂ => (s + 1 + n) / 2 := by fun_prop
  exact ((differentiable_const _).mul (Complex.differentiable_one_div_Gamma.comp hw)).mul
    ((differentiable_lowerDual hc hu₀).comp (hw.sub_const 1))

lemma half_shift_odd (s : ℂ) (n : ℕ) : (s + 1 + n) / 2 = (s + ((n + 1 : ℕ) : ℂ)) / 2 := by
  push_cast; ring

lemma dSeriesOdd_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {c u₀ S : ℝ} (hu₀ : 0 < u₀)
    (hS0 : 0 ≤ S) (hS : ∀ u ∈ Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) ≤ S) (s₀ : ℂ) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧ ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1,
      ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ *
        ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
          ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖ ≤ b n := by
  obtain ⟨N, C, hC0, hN⟩ := local_gamma_control s₀
  obtain ⟨Ca, hCa⟩ := ha
  have hCa0 : 0 ≤ Ca := le_trans (norm_nonneg _) (by simpa using hCa 0)
  set l : ℝ := 1 / (4 * (R ^ 2 + 1)) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; nlinarith
  have hq : R * √l < 1 := by
    have h1 : (R * √l) ^ 2 < 1 := by
      rw [mul_pow, Real.sq_sqrt hl0.le, hl]
      rw [← mul_div_assoc, mul_one, div_lt_one (by positivity)]; nlinarith
    nlinarith [Real.sqrt_nonneg l, mul_nonneg hR (Real.sqrt_nonneg l)]
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (5 - s₀.re)
  refine ⟨max N N₂, fun n => Ca * C * S * rexp (u₀ / l) * l ^ ((s₀.re - 2) / 2) * (R * √l) ^ n,
    ?_, fun n hn s hs => ?_⟩
  · exact (summable_geometric_of_lt_one (mul_nonneg hR (Real.sqrt_nonneg _)) hq).mul_left _
  obtain ⟨-, h2, h3⟩ := hN (n + 1) (by have := le_of_max_le_left hn; omega) s hs
  rw [← half_shift_odd] at h2 h3
  have hn2 : (N₂ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  set w := (s + 1 + n) / 2 with hw
  set y := (w - 1).re with hy
  have hxy : w.re = y + 1 := by simp [hy]
  have hy1 : 1 ≤ y := by
    have : (s₀.re - 1 + ((n + 1 : ℕ) : ℝ)) / 2 ≤ w.re := h2
    push_cast at this; linarith
  have hy0 : 0 < y := by linarith
  have hG := Real.Gamma_pos_of_pos (show 0 < y + 1 by linarith)
  have hI := integral_norm_lowerDual_le hu₀ (w := w - 1) hy0 hS
  have hΓ : ‖(Complex.Gamma w)⁻¹‖ ≤ C / Real.Gamma (y + 1) := by
    rw [le_div_iff₀ hG, ← hxy]; exact h3
  have hE := rpow_div_Gamma_le hy0 hu₀.le hl0
  have hpow : l ^ y ≤ l ^ ((s₀.re - 2) / 2) * (√l) ^ n := by
    rw [← rpow_half_add_nat hl0]
    apply Real.rpow_le_rpow_of_exponent_ge hl0 hl1
    have : (s₀.re - 1 + ((n + 1 : ℕ) : ℝ)) / 2 ≤ w.re := h2
    push_cast at this; linarith
  calc ‖a n‖ * ‖(Complex.Gamma w)⁻¹‖ * ∫ u in Ioc 0 u₀, _
      ≤ ‖a n‖ * ‖(Complex.Gamma w)⁻¹‖ * (S * (u₀ ^ y / y)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ (Ca * R ^ n) * (C / Real.Gamma (y + 1)) * (S * (u₀ ^ y / 1)) := by
        refine mul_le_mul (mul_le_mul (hCa n) hΓ (by positivity) (by positivity)) ?_
          (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) one_pos hy1)
          hS0
    _ = Ca * R ^ n * C * S * (u₀ ^ y / Real.Gamma (y + 1)) := by field_simp
    _ ≤ Ca * R ^ n * C * S * (rexp (u₀ / l) * (l ^ ((s₀.re - 2) / 2) * (√l) ^ n)) := by
        apply mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
        positivity
    _ = _ := by simp only [mul_pow]; ring

lemma weight_odd_eq {c u : ℝ} (hu : 0 < u) (w : ℂ) :
    ((u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * (u : ℂ) ^ (w - 1) =
      (u : ℂ) ^ (w - 1 - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) := by
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  have h32 : u ^ (-(3 / 2 : ℝ)) = u ^ (-(1 / 2 : ℝ)) * u⁻¹ := by
    rw [show -(3 / 2 : ℝ) = -(1 / 2) + -1 by norm_num, Real.rpow_add hu, Real.rpow_neg_one]
  have hw : (u : ℂ) ^ (w - 1 - 1) = (u : ℂ) ^ (w - 1) * (u : ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hu', Complex.cpow_one, div_eq_mul_inv]
  rw [h32, hw]
  push_cast
  ring

/-- `Z_{3/2}[h_{s+1}](c)` as a series, for every `s`. -/
theorem hasSum_dSeriesOdd (ha : GeomBounded a R) (hR : 0 ≤ R) {c u₀ : ℝ} (hc : 0 < c)
    (hu₀ : 0 < u₀) (s : ℂ) :
    HasSum (fun n => dSeriesTermOdd a c u₀ n s)
      (∫ u in Ioc 0 u₀, ((u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernel a (s + 1) u) := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeriesOdd_local_bound ha hR hu₀ hS0 (hS c le_rfl) s
  have e : ∀ n, ∀ u ∈ Ioc (0 : ℝ) u₀,
      ((u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a (s + 1) n u =
      (a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹) *
        ((u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)) := by
    intro n u hu
    unfold kernelTerm
    rw [← weight_odd_eq hu.1]; ring
  have hint : ∀ n, IntegrableOn
      (fun u => ((u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a (s + 1) n u)
      (Ioc 0 u₀) := fun n => by
    have h1 : IntegrableOn (fun u : ℝ => (a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹) *
        ((u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)))
        (Ioc 0 u₀) := (integrableOn_lowerDual hc hu₀ _).const_mul _
    exact h1.congr_fun (fun u hu => (e n u hu).symm) measurableSet_Ioc
  have hnorm : ∀ n, ∫ u in Ioc 0 u₀,
      ‖((u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a (s + 1) n u‖ =
      ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀,
        ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
          ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖ := fun n => by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu => by rw [e n u hu]), ← norm_mul,
      ← integral_const_mul]
    congr 1; funext u; rw [norm_mul, norm_mul, norm_mul, mul_assoc]
  have hsum : Summable fun n => ∫ u in Ioc 0 u₀,
      ‖((u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a (s + 1) n u‖ := by
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_nat_add_iff N).2 hb)
    rw [hnorm]; exact hbn (n + N) (Nat.le_add_left _ _) s (Metric.mem_ball_self one_pos)
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext n
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu => e n u hu), integral_const_mul]; rfl
  · congr 1; funext u; rw [kernel, ← tsum_mul_left]

lemma differentiable_dualTermOdd (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 0 < m) :
    Differentiable ℂ fun s => dualTermOdd (kernel a (s + 1)) u₀ lam m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < lam * (m : ℝ) ^ 2 := by positivity
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  have e : (fun s => dualTermOdd (kernel a (s + 1)) u₀ lam m) =
      fun s => ∑' n, dSeriesTermOdd a (lam * (m : ℝ) ^ 2) u₀ n s :=
    funext fun s => ((hasSum_dSeriesOdd ha hR hc hu₀ s).tsum_eq).symm
  rw [e]
  refine differentiable_tsum_of_local_bound (fun n => differentiable_dSeriesTermOdd hc hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := dSeriesOdd_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  refine ⟨N, b, hb, fun n hn s hs => ?_⟩
  refine le_trans ?_ (hbn n hn s hs)
  unfold dSeriesTermOdd lowerDual
  rw [norm_mul, norm_mul]
  gcongr
  exact norm_integral_le_integral_norm _

theorem dualTermOdd_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {lam : ℝ} (hlam : 0 < lam) (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ m : ℕ, 1 ≤ m →
      ‖dualTermOdd (kernel a (s + 1)) u₀ lam m‖ ≤ rexp (-((m : ℝ) ^ 2 - 1) * (lam / u₀)) * B := by
  have hc₁ : (0 : ℝ) < lam := hlam
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc₁ u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeriesOdd_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  have hsmall : ∀ n, ∃ G, ∀ s ∈ Metric.ball s₀ 1, ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ *
      ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)) : ℝ) : ℂ)‖ ≤ G := by
    intro n
    obtain ⟨G, hG⟩ := exists_bound_inv_Gamma_ball s₀ (n + 1)
    simp only [← half_shift_odd] at hG
    set x₀ := ((s₀ + 1 + n) / 2 - 1).re
    set K := ∫ u in Ioc 0 u₀, (u ^ (x₀ - 3 / 2) + u ^ (x₀ - 1 / 2)) *
      (u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)))
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
      have hnear := re_half_near hs (n + 1)
      simp only [← half_shift_odd] at hnear
      exact mul_le_mul_of_nonneg_right (rpow_le_add_of_near hu.1 (by simpa [x₀] using hnear))
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
  have hc : 0 < lam * (m : ℝ) ^ 2 := by positivity
  have hsum := hasSum_dSeriesOdd ha hR hc hu₀ s
  set E := rexp (-((m : ℝ) ^ 2 - 1) * (lam / u₀))
  unfold dualTermOdd
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖dSeriesTermOdd a (lam * (m : ℝ) ^ 2) u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)) : ℝ) : ℂ)‖) := by
    unfold dSeriesTermOdd lowerDual
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
    have hexp : rexp (-(lam * (m : ℝ) ^ 2 / u)) ≤ E * rexp (-(lam / u)) := by
      simp only [E]
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : lam * ((m : ℝ) ^ 2 - 1) / u₀ ≤ lam * ((m : ℝ) ^ 2 - 1) / u :=
        div_le_div_of_nonneg_left (mul_nonneg hlam.le (by nlinarith)) hu.1 hu.2
      have e : lam * (m : ℝ) ^ 2 / u = lam * ((m : ℝ) ^ 2 - 1) / u + lam / u := by ring
      rw [e]
      have e2 : -((m : ℝ) ^ 2 - 1) * (lam / u₀) = -(lam * ((m : ℝ) ^ 2 - 1) / u₀) := by ring
      rw [e2]; linarith
    set P := ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1)‖
    have hP : 0 ≤ P := norm_nonneg _
    calc P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(lam * (m : ℝ) ^ 2 / u)))
        = (u ^ (-(1 / 2 : ℝ)) * P) * rexp (-(lam * (m : ℝ) ^ 2 / u)) := by ring
      _ ≤ (u ^ (-(1 / 2 : ℝ)) * P) * (E * rexp (-(lam / u))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hr hP)
      _ = E * (P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(lam / u)))) := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs



/-- `s ↦ ∑_{m ≥ 1} d_m Z_{3/2}[h_{s+1}](λ m²)` is entire for `|d_m| ≤ B(m+1)`. -/
theorem differentiable_sum_dualTermOdd (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ}
    (hu₀ : 0 < u₀) {lam : ℝ} (hlam : 0 < lam) {d : ℕ → ℂ} {B : ℝ}
    (hd : ∀ m, ‖d m‖ ≤ B * ((m : ℝ) + 1)) :
    Differentiable ℂ fun s => ∑' m : ℕ, d (m + 1) * dualTermOdd (kernel a (s + 1)) u₀ lam (m + 1) := by
  have hT : ∀ m : ℕ, Differentiable ℂ fun s =>
      d (m + 1) * dualTermOdd (kernel a (s + 1)) u₀ lam (m + 1) :=
    fun m => (differentiable_dualTermOdd ha hR hu₀ hlam (Nat.succ_pos m)).const_mul _
  refine differentiable_tsum_of_local_bound hT fun s₀ => ?_
  obtain ⟨B₁, hB₁⟩ := dualTermOdd_local_bound ha hR hu₀ hlam s₀
  have hB₁0 : 0 ≤ B₁ := by
    have := (norm_nonneg _).trans (hB₁ s₀ (Metric.mem_ball_self one_pos) 1 le_rfl)
    simpa using this
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hd 0); simpa using this
  have hc : 0 < lam / u₀ := by positivity
  have hr : ‖rexp (-(lam / u₀))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one 0 hr
  refine ⟨0, fun m => B * B₁ * ((m : ℝ) ^ 1 * rexp (-(lam / u₀)) ^ m + 2 * ((m : ℝ) ^ 0 *
    rexp (-(lam / u₀)) ^ m)), ((hs1.add (hs0.mul_left _)).mul_left _), fun m _ s hs => ?_⟩
  rw [norm_mul]
  have h1 := hB₁ s hs (m + 1) (Nat.le_add_left _ _)
  have h2 := exp_shift_le hc 1 m 1
  simp only [Nat.cast_one, one_pow, sub_self, neg_zero, zero_mul, Real.exp_zero, one_mul] at h2
  have hdm := hd (m + 1)
  calc ‖d (m + 1)‖ * ‖dualTermOdd (kernel a (s + 1)) u₀ lam (m + 1)‖
      ≤ (B * (((m + 1 : ℕ) : ℝ) + 1)) * (rexp (-(lam / u₀)) ^ m * B₁) := by
        refine mul_le_mul hdm (h1.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h2 hB₁0
    _ = _ := by push_cast; ring

/-! ### The continuation for odd and for arbitrary periodic weights -/

lemma mainTermOdd_eq_gen (h : ℝ → ℂ) (u₀ : ℝ) (c : ℕ → ℂ) (k₀ : ℕ) :
    mainTermOdd h u₀ c k₀ = mainTermGen h u₀ c 0 0 k₀ := by
  unfold mainTermOdd mainTermGen mainWeightGen
  congr 1; funext u; simp

/-- The points `s` with `s + 1 ∉ {1, 0, -1, …}`. -/
def oddDomain : Set ℂ := {s : ℂ | s + 1 ∈ notPoles}

lemma notPoles_subset_oddDomain : notPoles ⊆ oddDomain := fun s hs n h =>
  hs (n + 1) (by push_cast; linear_combination h)

/-- The right-hand side of the odd twisted splitting, continued to `ℂ ∖ {0, -1, -2, …}`. -/
noncomputable def twistedOddRHS (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (q : ℕ) (χ : ℤ → ℂ) (s : ℂ) : ℂ :=
  (∑' k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * ((k + k₀ : ℕ) : ℂ) * kTerm (kernel a (s + 1)) u₀ (k + k₀)) +
    (∑' m : ℕ, charDualOdd q χ (m + 1) *
      dualTermOdd (kernel a (s + 1)) u₀ (π ^ 2 / q ^ 2) (m + 1)) +
    twistMainCont a u₀ (fun k => χ k * k) 0 0 k₀ (s + 1)

theorem differentiableOn_twistedOddRHS (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ}
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ}
    (hper : Function.Periodic χ q) :
    DifferentiableOn ℂ (twistedOddRHS a k₀ u₀ q χ) oddDomain := by
  set Bχ := ∑ a ∈ range q, ‖χ a‖
  have hB0 : 0 ≤ Bχ := sum_nonneg fun _ _ => norm_nonneg _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hk := differentiable_sum_kTerm_weighted ha hR hRk hu₀ (w := fun k : ℕ => χ k * k)
    (B := Bχ) (fun k => by
      rw [norm_mul, Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_right (periodic_bound hq hper k) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (by linarith) hB0)) 1
  have hd := differentiable_sum_dualTermOdd ha hR hu₀ (lam := π ^ 2 / q ^ 2) (by positivity)
    (d := charDualOdd q χ) (B := π * √π / q ^ 2 * Bχ) (fun m => by
      rw [charDualOdd, norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_natCast]
      have := gaussSum_norm_le (q := q) χ m
      have h0 : 0 ≤ π * √π / q ^ 2 := by positivity
      calc π * √π / q ^ 2 * m * ‖gaussSum q χ m‖ ≤ π * √π / q ^ 2 * m * Bχ :=
            mul_le_mul_of_nonneg_left this (mul_nonneg h0 (Nat.cast_nonneg _))
        _ ≤ π * √π / q ^ 2 * Bχ * ((m : ℝ) + 1) := by nlinarith)
  have hmain : DifferentiableOn ℂ (fun s => twistMainCont a u₀ (fun k => χ k * k) 0 0 k₀ (s + 1))
      oddDomain :=
    (differentiableOn_twistMainCont ha hR hu₀ _ _ _ k₀).comp
      (differentiable_id.add_const 1).differentiableOn fun s hs => hs
  exact (hk.differentiableOn.add hd.differentiableOn).add hmain

theorem zetaTail_char_odd_eq_twistedOddRHS (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ}
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ}
    (hs : 2 < s.re) {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (hodd : ∀ k, χ (-k) = -χ k) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    zetaTail (fun k => χ k * F k) k₀ s = twistedOddRHS a k₀ u₀ q χ s := by
  rw [zetaTail_split_char_odd ha hR hk₀ hRk hF hs hq hper hodd hu₀, twistedOddRHS,
    twistMainCont_eq ha hR hu₀ _ _ _ k₀ (by simp; linarith), mainTermOdd_eq_gen]

/-- The right-hand side of Remark 3.7 for an arbitrary periodic weight. -/
noncomputable def twistedRHS (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (q : ℕ) (χ : ℤ → ℂ) (s : ℂ) : ℂ :=
  twistedEvenRHS a k₀ u₀ q (evenPart χ) s + twistedOddRHS a k₀ u₀ q (oddPart χ) s

/-- **Remark 3.7, continuation**: for every `q`-periodic `χ`, the tail `L_F^{≥k₀}(s, χ)` continues
holomorphically to `ℂ ∖ {1, 0, -1, …}` and is given there by the twisted splitting. -/
theorem zetaTail_periodic_continuation (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ}
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {q : ℕ}
    (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    DifferentiableOn ℂ (twistedRHS a k₀ u₀ q χ) notPoles ∧
      ∀ s : ℂ, 2 < s.re → twistedRHS a k₀ u₀ q χ s = zetaTail (fun k => χ k * F k) k₀ s := by
  refine ⟨(differentiableOn_twistedEvenRHS ha hR hRk hu₀ hq (periodic_evenPart hper)).add
    ((differentiableOn_twistedOddRHS ha hR hRk hu₀ hq (periodic_oddPart hper)).mono
      notPoles_subset_oddDomain), fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  rw [zetaTail_split_periodic ha hR hk₀ hRk hF hs hq hper hu₀, twistedRHS,
    ← zetaTail_char_eq_twistedEvenRHS ha hR hk₀ hRk hF hs1 hq (periodic_evenPart hper)
      (evenPart_neg χ) hu₀,
    ← zetaTail_char_odd_eq_twistedOddRHS ha hR hk₀ hRk hF hs hq (periodic_oddPart hper)
      (oddPart_neg χ) hu₀,
    zetaTail_split_char ha hR hk₀ hRk hF hs1 hq (periodic_evenPart hper) (evenPart_neg χ) hu₀,
    zetaTail_split_char_odd ha hR hk₀ hRk hF hs hq (periodic_oddPart hper) (oddPart_neg χ) hu₀]

end ZetaF
