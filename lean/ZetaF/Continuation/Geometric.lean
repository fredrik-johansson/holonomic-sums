/-
# Theorem 4.1(1) on the unit circle, for all `s`

For real `α ∉ ℤ` and `z = e^{2πiα}`, every piece of the polylogarithm splitting is entire in `s`:
the `k`-terms with weights `C_k`, `k S_k`, the dual terms `J^{(δ)}(c_n)` (all `c_n ≥ π² dist(α,ℤ)² > 0`),
`H(s)` and `L_k(s)`.  Hence `Li_F^{≥k₀}(s, z)` extends to an entire function of `s`, given by the
splitting (`polylogTail_entire`).  We also show that `L_k(s) = ∫₀^{u₀} e^{-k²u} h_s` is entire.
-/
import ZetaF.Continuation.Twisted
import ZetaF.Polylog.Geometric

open MeasureTheory Set Filter Finset
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-! ### Dual integrals with a general dual point -/

theorem dualJ_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ c : ℝ, c₁ ≤ c →
      ‖∫ u in Ioc 0 u₀, ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernel a s u‖ ≤
        rexp (-((c - c₁) / u₀)) * B := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc₁ u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  have hsmall : ∀ n, ∃ G, ∀ s ∈ Metric.ball s₀ 1, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
      ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)) : ℝ) : ℂ)‖ ≤ G := by
    intro n
    obtain ⟨G, hG⟩ := exists_bound_inv_Gamma_ball s₀ n
    set x₀ := ((s₀ + n) / 2).re
    set K := ∫ u in Ioc 0 u₀, (u ^ (x₀ - 3 / 2) + u ^ (x₀ - 1 / 2)) *
      (u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)))
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
  refine ⟨∑' n, g n, fun s hs c hc => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le hc₁ hc
  have hsum := hasSum_dSeries ha hR hc0 hu₀ s
  set E := rexp (-((c - c₁) / u₀))
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖dSeriesTerm a c u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)) : ℝ) : ℂ)‖) := by
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
    have hexp : rexp (-(c / u)) ≤ E * rexp (-(c₁ / u)) := by
      simp only [E]
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : (c - c₁) / u₀ ≤ (c - c₁) / u :=
        div_le_div_of_nonneg_left (by linarith) hu.1 hu.2
      have e : c / u = (c - c₁) / u + c₁ / u := by ring
      rw [e]; linarith
    set P := ‖(u : ℂ) ^ ((s + n) / 2 - 1)‖
    have hP : 0 ≤ P := norm_nonneg _
    calc P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)))
        = (u ^ (-(1 / 2 : ℝ)) * P) * rexp (-(c / u)) := by ring
      _ ≤ (u ^ (-(1 / 2 : ℝ)) * P) * (E * rexp (-(c₁ / u))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hr hP)
      _ = E * (P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)))) := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs

theorem dualJOdd_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ c : ℝ, c₁ ≤ c →
      ‖∫ u in Ioc 0 u₀, ((u ^ (-(3 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernel a (s + 1) u‖ ≤
        rexp (-((c - c₁) / u₀)) * B := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc₁ u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeriesOdd_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  have hsmall : ∀ n, ∃ G, ∀ s ∈ Metric.ball s₀ 1, ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ *
      ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)) : ℝ) : ℂ)‖ ≤ G := by
    intro n
    obtain ⟨G, hG⟩ := exists_bound_inv_Gamma_ball s₀ (n + 1)
    simp only [← half_shift_odd] at hG
    set x₀ := ((s₀ + 1 + n) / 2 - 1).re
    set K := ∫ u in Ioc 0 u₀, (u ^ (x₀ - 3 / 2) + u ^ (x₀ - 1 / 2)) *
      (u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)))
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
  refine ⟨∑' n, g n, fun s hs c hc => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le hc₁ hc
  have hsum := hasSum_dSeriesOdd ha hR hc0 hu₀ s
  set E := rexp (-((c - c₁) / u₀))
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖dSeriesTermOdd a c u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)) : ℝ) : ℂ)‖) := by
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
    have hexp : rexp (-(c / u)) ≤ E * rexp (-(c₁ / u)) := by
      simp only [E]
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : (c - c₁) / u₀ ≤ (c - c₁) / u :=
        div_le_div_of_nonneg_left (by linarith) hu.1 hu.2
      have e : c / u = (c - c₁) / u + c₁ / u := by ring
      rw [e]; linarith
    set P := ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1)‖
    have hP : 0 ≤ P := norm_nonneg _
    calc P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)))
        = (u ^ (-(1 / 2 : ℝ)) * P) * rexp (-(c / u)) := by ring
      _ ≤ (u ^ (-(1 / 2 : ℝ)) * P) * (E * rexp (-(c₁ / u))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hr hP)
      _ = E * (P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)))) := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs

/-! ### `L_k(s) = ∫₀^{u₀} e^{-k²u} h_s` is entire -/

/-- A term of the series for `L_k(s)`. -/
noncomputable def lSeriesTerm (a : ℕ → ℂ) (u₀ : ℝ) (k n : ℕ) (s : ℂ) : ℂ :=
  a n * ((k : ℂ) ^ (-2 * ((s + n) / 2)) -
    (Complex.Gamma ((s + n) / 2))⁻¹ * upperLaplace ((k : ℝ) ^ 2) u₀ ((s + n) / 2))

lemma mainSeriesTerm_sub_succ {u₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (n : ℕ) (s : ℂ) :
    mainSeriesTerm a u₀ k n s - mainSeriesTerm a u₀ (k + 1) n s = lSeriesTerm a u₀ k n s := by
  unfold mainSeriesTerm lSeriesTerm
  rw [sum_Ico_succ_top hk]; ring

lemma differentiable_lSeriesTerm {u₀ : ℝ} (hu₀ : 0 < u₀) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    Differentiable ℂ (lSeriesTerm a u₀ k n) := by
  intro s
  have hw : DifferentiableAt ℂ (fun s : ℂ => (s + n) / 2) s := (differentiable_half_shift n) s
  have hΓ : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma ((s + n) / 2))⁻¹) s :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp s hw
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk' : 0 < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  exact (((hw.const_mul (-2)).const_cpow (Or.inl hk0)).sub
    (hΓ.mul ((differentiable_upperLaplace hk' hu₀).differentiableAt.comp s hw))).const_mul _

lemma lSeries_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {k : ℕ} (hk : 1 ≤ k) (s₀ : ℂ) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧ ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1,
      ‖lSeriesTerm a u₀ k n s‖ ≤ b n := by
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
  obtain ⟨h1, h2, h3⟩ := hN n hn s hs
  set w := (s + n) / 2 with hw
  set x := w.re
  have hx0 : 0 < x := by linarith
  have hG := Real.Gamma_pos_of_pos hx0
  have hΓ : ‖(Complex.Gamma w)⁻¹‖ ≤ C / Real.Gamma x := by rw [le_div_iff₀ hG]; exact h3
  have hxΓ : x * Real.Gamma x = Real.Gamma (x + 1) := (Real.Gamma_add_one hx0.ne').symm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hid := cpow_sub_upperLaplace (k := (k : ℝ)) hk0 hu₀ hx0
  simp only [Complex.ofReal_natCast] at hid
  have hE := rpow_div_Gamma_le hx0 hu₀.le hl0
  have hpow : l ^ x ≤ l ^ ((s₀.re - 1) / 2) * (√l) ^ n := by
    rw [← rpow_half_add_nat hl0]
    exact Real.rpow_le_rpow_of_exponent_ge hl0 hl1 (by linarith)
  unfold lSeriesTerm
  rw [← hw, hid, norm_mul, norm_mul]
  calc ‖a n‖ * (‖(Complex.Gamma w)⁻¹‖ * ‖lowerLaplace ((k : ℝ) ^ 2) u₀ w‖)
      ≤ (Ca * R ^ n) * ((C / Real.Gamma x) * (u₀ ^ x / x)) :=
        mul_le_mul (hCa n) (mul_le_mul hΓ (norm_lowerLaplace_le (by positivity) hu₀ hx0)
          (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = (Ca * R ^ n) * (C * (u₀ ^ x / Real.Gamma (x + 1))) := by rw [← hxΓ]; field_simp
    _ ≤ (Ca * R ^ n) * (C * (rexp (u₀ / l) * (l ^ ((s₀.re - 1) / 2) * (√l) ^ n))) := by
        gcongr; exact hE.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = _ := by simp only [mul_pow]; ring

/-- **`L_k(s)` is entire** (`k ≥ 1`). -/
theorem differentiable_lSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {k : ℕ} (hk : 1 ≤ k) : Differentiable ℂ fun s => ∑' n, lSeriesTerm a u₀ k n s :=
  differentiable_tsum_of_local_bound (fun n => differentiable_lSeriesTerm hu₀ hk n)
    (lSeries_local_bound ha hR hu₀ hk)

lemma integrableOn_mainWeight_mul {h : ℝ → ℂ} {u₀ : ℝ} (hcont : ContinuousOn h (Ioi 0))
    (hnear : IntegrableOn (fun u => u ^ (-(1 / 2 : ℝ)) * ‖h u‖) (Ioc 0 u₀))
    (hn0 : IntegrableOn (fun u => ‖h u‖) (Ioc 0 u₀)) (k : ℕ) :
    IntegrableOn (fun u => (mainWeight k u : ℂ) * h u) (Ioc 0 u₀) := by
  have hg : IntegrableOn (fun u => (1 / 2 * √π * u ^ (-(1 / 2 : ℝ)) + ((k : ℝ) + 1)) * ‖h u‖)
      (Ioc 0 u₀) := by
    have h1 : IntegrableOn (fun u => 1 / 2 * √π * (u ^ (-(1 / 2 : ℝ)) * ‖h u‖) +
        ((k : ℝ) + 1) * ‖h u‖) (Ioc 0 u₀) :=
      (hnear.const_mul (1 / 2 * √π)).add (hn0.const_mul ((k : ℝ) + 1))
    exact h1.congr_fun (fun u _ => by ring) measurableSet_Ioc
  exact integrableOn_weight_mul_of_le hcont (continuousOn_mainWeight k) Ioc_subset_Ioi_self
    measurableSet_Ioc hg (fun u hu => abs_mainWeight_le hu.1)

/-- `L_k(s) = ∑_n (…)` for `Re s > 1`. -/
theorem hasSum_lSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) {k : ℕ}
    (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => lSeriesTerm a u₀ k n s) (lowerL (kernel a s) u₀ k) := by
  have hs0 : 0 < s.re := by linarith
  have h := (hasSum_mainSeries ha hR hu₀ k hs).sub (hasSum_mainSeries ha hR hu₀ (k + 1) hs)
  simp only [mainSeriesTerm_sub_succ hk] at h
  convert h using 1
  have hc := continuousOn_kernel ha hR hs0 (a := a)
  have hn := integrableOn_rpow_neg_half_mul_norm_kernel ha hR hs hu₀ (a := a)
  have h0 := integrableOn_norm_kernel ha hR hs0 hu₀ (a := a)
  unfold mainTerm lowerL
  rw [← integral_sub (integrableOn_mainWeight_mul hc hn h0 k)
    (integrableOn_mainWeight_mul hc hn h0 (k + 1))]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [← sub_mul, ← Complex.ofReal_sub, mainWeight_sub_succ hk]

/-! ### The polylogarithm splitting for all `s` -/

lemma summable_kTerm_weighted (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ}
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) {w : ℕ → ℂ} {B : ℝ}
    (hw : ∀ k, ‖w k‖ ≤ B * ((k : ℝ) + 1)) (s : ℂ) :
    Summable fun k : ℕ => w (k + k₀) * kTerm (kernel a s) u₀ (k + k₀) := by
  obtain ⟨B₁, hB₁⟩ := kTerm_local_bound ha hR hRk hu₀ s
  have hB₁0 : 0 ≤ B₁ := by
    have := (norm_nonneg _).trans (hB₁ s (Metric.mem_ball_self one_pos) k₀ le_rfl)
    simpa using this
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans (hw 0); simpa using this
  have hr : ‖rexp (-u₀)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one 0 hr
  refine Summable.of_norm_bounded (((hs1.add (hs0.mul_left ((k₀ : ℝ) + 1))).mul_left (B * B₁)))
    fun k => ?_
  rw [norm_mul]
  have h1 := hB₁ s (Metric.mem_ball_self one_pos) (k + k₀) (Nat.le_add_left _ _)
  have h2 := exp_shift_le hu₀ k₀ k ((k₀ : ℝ) ^ 2)
  rw [sub_self, neg_zero, zero_mul, Real.exp_zero, one_mul] at h2
  calc ‖w (k + k₀)‖ * ‖kTerm (kernel a s) u₀ (k + k₀)‖
      ≤ (B * (((k + k₀ : ℕ) : ℝ) + 1)) * (rexp (-u₀) ^ k * B₁) := by
        refine mul_le_mul (hw _) (h1.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h2 hB₁0
    _ = _ := by push_cast; ring

lemma differentiable_geoJ0 (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {c : ℝ} (hc : 0 < c) : Differentiable ℂ fun s => geoJ (kernel a s) u₀ (1 / 2) c := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  have e : (fun s => geoJ (kernel a s) u₀ (1 / 2) c) = fun s => ∑' n, dSeriesTerm a c u₀ n s :=
    funext fun s => ((hasSum_dSeries ha hR hc hu₀ s).tsum_eq).symm
  rw [e]
  refine differentiable_tsum_of_local_bound (fun n => differentiable_dSeriesTerm hc hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  refine ⟨N, b, hb, fun n hn s hs => le_trans ?_ (hbn n hn s hs)⟩
  unfold dSeriesTerm lowerDual
  rw [norm_mul, norm_mul]
  gcongr
  exact norm_integral_le_integral_norm _

lemma differentiable_geoJ1 (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {c : ℝ} (hc : 0 < c) : Differentiable ℂ fun s => geoJ (kernel a (s + 1)) u₀ (3 / 2) c := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  have e : (fun s => geoJ (kernel a (s + 1)) u₀ (3 / 2) c) =
      fun s => ∑' n, dSeriesTermOdd a c u₀ n s :=
    funext fun s => ((hasSum_dSeriesOdd ha hR hc hu₀ s).tsum_eq).symm
  rw [e]
  refine differentiable_tsum_of_local_bound (fun n => differentiable_dSeriesTermOdd hc hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := dSeriesOdd_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  refine ⟨N, b, hb, fun n hn s hs => le_trans ?_ (hbn n hn s hs)⟩
  unfold dSeriesTermOdd lowerDual
  rw [norm_mul, norm_mul]
  gcongr
  exact norm_integral_le_integral_norm _

/-- For `α ∉ ℤ`, all dual points satisfy `c_n ≥ π² δ²`, `δ = dist(α, ℤ) > 0`. -/
lemma geoDual_ge {α : ℝ} (hα : ∀ m : ℤ, α ≠ m) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ n : ℤ, c₁ ≤ geoDual α n := by
  set f := Int.fract α
  have hf0 : 0 < f := by
    rcases (Int.fract_nonneg α).lt_or_eq with h | h
    · exact h
    · exact absurd (show α = (⌊α⌋ : ℝ) by linarith [Int.floor_add_fract α]) (hα ⌊α⌋)
  have hf1 : f < 1 := Int.fract_lt_one α
  set δ := min f (1 - f)
  have hδ : 0 < δ := lt_min hf0 (by linarith)
  refine ⟨π ^ 2 * δ ^ 2, by positivity, fun n => ?_⟩
  unfold geoDual
  have hαe : α = ⌊α⌋ + f := (Int.floor_add_fract α).symm
  have key : δ ≤ |(n : ℝ) - α| := by
    rw [hαe]
    rcases le_or_gt (n - ⌊α⌋) 0 with h | h
    · have : ((n - ⌊α⌋ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
      push_cast at this
      rw [abs_of_neg (by linarith)]
      linarith [min_le_left f (1 - f)]
    · have : (1 : ℝ) ≤ ((n - ⌊α⌋ : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at this
      rw [abs_of_pos (by linarith)]
      linarith [min_le_right f (1 - f)]
  have : δ ^ 2 ≤ ((n : ℝ) - α) ^ 2 := by
    rw [← sq_abs ((n : ℝ) - α)]; exact pow_le_pow_left₀ hδ.le key 2
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- The right-hand side of Theorem 4.1(1) with `H` and `L_k` replaced by their entire series. -/
noncomputable def polylogRHS (a : ℕ → ℂ) (k₀ : ℕ) (u₀ α : ℝ) (s : ℂ) : ℂ :=
  (∑' k : ℕ, (geoC (Complex.exp (2 * π * Complex.I * α)) (k + k₀) *
      kTerm (kernel a s) u₀ (k + k₀) +
    ((k + k₀ : ℕ) : ℂ) * geoS (Complex.exp (2 * π * Complex.I * α)) (k + k₀) *
      kTerm (kernel a (s + 1)) u₀ (k + k₀))) +
  ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, (geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) -
    Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ) * geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) -
  1 / 2 * (∑' n, hSeriesTerm a u₀ n s) -
  ∑ k ∈ Finset.Ico 1 k₀, (geoC (Complex.exp (2 * π * Complex.I * α)) k *
      (∑' n, lSeriesTerm a u₀ k n s) +
    (k : ℂ) * geoS (Complex.exp (2 * π * Complex.I * α)) k * (∑' n, lSeriesTerm a u₀ k n (s + 1)))

/-- **Theorem 4.1(1) on the unit circle, for all `s`**: for real `α ∉ ℤ` and `z = e^{2πiα}`,
the splitting defines an entire function of `s` which equals `Li_F^{≥k₀}(s, z)` for `Re s > 2`.
In particular `Li_F^{≥k₀}(·, z)` extends to an entire function. -/
theorem polylogTail_entire (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {α : ℝ}
    (hα : ∀ m : ℤ, α ≠ m) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Differentiable ℂ (polylogRHS a k₀ u₀ α) ∧ ∀ s : ℂ, 2 < s.re →
      polylogRHS a k₀ u₀ α s =
        zetaTail (fun k => F k * Complex.exp (2 * π * Complex.I * α) ^ k) k₀ s := by
  set z := Complex.exp (2 * π * Complex.I * α) with hz_def
  have hz : ‖z‖ = 1 := by
    rw [hz_def, show 2 * π * Complex.I * (α : ℂ) = ((2 * π * α : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hC : ∀ k : ℕ, ‖geoC z k‖ ≤ 1 * ((k : ℝ) + 1) := fun k =>
    (norm_geoC_le hz k).trans (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hS : ∀ k : ℕ, ‖(k : ℂ) * geoS z k‖ ≤ 1 * ((k : ℝ) + 1) := fun k => by
    rw [norm_mul, Complex.norm_natCast]
    calc (k : ℝ) * ‖geoS z k‖ ≤ k * 1 :=
          mul_le_mul_of_nonneg_left (norm_geoS_le hz k) (Nat.cast_nonneg _)
      _ ≤ 1 * ((k : ℝ) + 1) := by linarith
  constructor
  · -- the `k`-terms
    have hkC := differentiable_sum_kTerm_weighted ha hR hRk hu₀ hC 0
    have hkS := differentiable_sum_kTerm_weighted ha hR hRk hu₀ hS 1
    simp only [add_zero] at hkC
    have hk : Differentiable ℂ fun s => ∑' k : ℕ, (geoC z (k + k₀) *
        kTerm (kernel a s) u₀ (k + k₀) + ((k + k₀ : ℕ) : ℂ) * geoS z (k + k₀) *
        kTerm (kernel a (s + 1)) u₀ (k + k₀)) := by
      have he : (fun s => ∑' k : ℕ, (geoC z (k + k₀) * kTerm (kernel a s) u₀ (k + k₀) +
          ((k + k₀ : ℕ) : ℂ) * geoS z (k + k₀) * kTerm (kernel a (s + 1)) u₀ (k + k₀))) =
          fun s => (∑' k : ℕ, geoC z (k + k₀) * kTerm (kernel a s) u₀ (k + k₀)) +
            ∑' k : ℕ, ((k + k₀ : ℕ) : ℂ) * geoS z (k + k₀) * kTerm (kernel a (s + 1)) u₀ (k + k₀) :=
        funext fun s => (summable_kTerm_weighted ha hR hRk hu₀ hC s).tsum_add
          (summable_kTerm_weighted ha hR hRk hu₀ hS (s + 1))
      rw [he]; exact hkC.add hkS
    -- the dual terms
    obtain ⟨c₁, hc₁, hc₁n⟩ := geoDual_ge hα
    have hcpos : ∀ n : ℤ, 0 < geoDual α n := fun n => lt_of_lt_of_le hc₁ (hc₁n n)
    set e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
    set T : ℤ → ℂ → ℂ := fun n s => geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) -
      Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ) * geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)
      with hT
    have hTd : ∀ n, Differentiable ℂ (T n) := fun n =>
      (differentiable_geoJ0 ha hR hu₀ (hcpos n)).sub
        ((differentiable_geoJ1 ha hR hu₀ (hcpos n)).const_mul _)
    have hdual : Differentiable ℂ fun s => ∑' n : ℤ, T n s := by
      have he : (fun s => ∑' n : ℤ, T n s) = fun s => ∑' m : ℕ, T (e m) s :=
        funext fun s => (e.tsum_eq (fun n => T n s)).symm
      rw [he]
      refine differentiable_tsum_of_local_bound (fun m => hTd (e m)) fun s₀ => ?_
      obtain ⟨B₀, hB₀⟩ := dualJ_local_bound ha hR hu₀ hc₁ s₀
      obtain ⟨B₁, hB₁⟩ := dualJOdd_local_bound ha hR hu₀ hc₁ s₀
      have hB₀0 : 0 ≤ B₀ := by
        have := (norm_nonneg _).trans (hB₀ s₀ (Metric.mem_ball_self one_pos) c₁ le_rfl)
        simpa using this
      have hB₁0 : 0 ≤ B₁ := by
        have := (norm_nonneg _).trans (hB₁ s₀ (Metric.mem_ball_self one_pos) c₁ le_rfl)
        simpa using this
      set g : ℤ → ℝ := fun n => rexp (c₁ / u₀) * (B₀ * rexp (-(geoDual α n / u₀)) +
        π * B₁ * (|(n : ℝ) - α| * rexp (-(geoDual α n / u₀))))
      have hg : Summable g := (((summable_geoDual α hu₀).mul_left B₀).add
        ((summable_abs_mul_geoDual α hu₀).mul_left (π * B₁))).mul_left _
      refine ⟨0, fun m => g (e m), e.summable_iff.2 hg, fun m _ s hs => ?_⟩
      have hexp : ∀ c : ℝ, rexp (-((c - c₁) / u₀)) = rexp (c₁ / u₀) * rexp (-(c / u₀)) :=
        fun c => by rw [← Real.exp_add]; congr 1; ring
      have h0 := hB₀ s hs (geoDual α (e m)) (hc₁n _)
      have h1 := hB₁ s hs (geoDual α (e m)) (hc₁n _)
      rw [hexp] at h0 h1
      simp only [hT, g]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs]
      have : geoJ (kernel a s) u₀ (1 / 2) (geoDual α (e m)) = ∫ u in Ioc 0 u₀,
          ((u ^ (-(1 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u)) : ℝ) : ℂ) * kernel a s u := rfl
      rw [this]
      have : geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α (e m)) = ∫ u in Ioc 0 u₀,
          ((u ^ (-(3 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u)) : ℝ) : ℂ) * kernel a (s + 1) u := rfl
      rw [this]
      have hpos : 0 ≤ |((e m : ℤ) : ℝ) - α| := abs_nonneg _
      calc _ ≤ rexp (c₁ / u₀) * rexp (-(geoDual α (e m) / u₀)) * B₀ +
            π * |((e m : ℤ) : ℝ) - α| * (rexp (c₁ / u₀) * rexp (-(geoDual α (e m) / u₀)) * B₁) :=
            add_le_add h0 (mul_le_mul_of_nonneg_left h1 (by positivity))
        _ = _ := by ring
    -- the main terms
    have hH := differentiable_hSeries ha hR hu₀ (a := a)
    have hL : ∀ k ∈ Finset.Ico 1 k₀, Differentiable ℂ fun s => geoC z k *
        (∑' n, lSeriesTerm a u₀ k n s) + (k : ℂ) * geoS z k * (∑' n, lSeriesTerm a u₀ k n (s + 1)) :=
      fun k hk => by
        have hk1 := (Finset.mem_Ico.1 hk).1
        exact ((differentiable_lSeries ha hR hu₀ hk1).const_mul _).add
          (((differentiable_lSeries ha hR hu₀ hk1).comp (differentiable_id.add_const 1)).const_mul _)
    unfold polylogRHS
    exact ((hk.add (hdual.const_mul _)).sub (hH.const_mul _)).sub (Differentiable.fun_sum hL)
  · intro s hs
    have hs1 : 1 < s.re := by linarith
    rw [polylogTail_split ha hR hk₀ hRk hF hs α hu₀, polylogRHS,
      (hasSum_hSeries ha hR hu₀ (by linarith)).tsum_eq]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 := (Finset.mem_Ico.1 hk).1
    rw [(hasSum_lSeries ha hR hu₀ hk1 hs1).tsum_eq,
      (hasSum_lSeries ha hR hu₀ hk1 (by simp; linarith)).tsum_eq]

/-! ### Odd periodic weights: an entire continuation -/

lemma mainTermOdd_eq_sum (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (c : ℕ → ℂ) (k₀ : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mainTermOdd (kernel a s) u₀ c k₀ = -∑ k ∈ Finset.Ico 1 k₀, c k * lowerL (kernel a s) u₀ k := by
  have hh : IntegrableOn (kernel a s) (Ioc 0 u₀) :=
    Integrable.mono' (integrableOn_norm_kernel ha hR hs hu₀)
      (((continuousOn_kernel ha hR hs).mono Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc) (Eventually.of_forall fun _ => le_rfl)
  have hL : ∀ k : ℕ, IntegrableOn (fun u => c k * ((rexp (-((k : ℝ) ^ 2 * u)) : ℂ) *
      kernel a s u)) (Ioc 0 u₀) := fun k => by
    have : IntegrableOn (fun u => 1 * ‖kernel a s u‖) (Ioc 0 u₀) := by
      simpa using integrableOn_norm_kernel ha hR hs hu₀
    exact (integrableOn_weight_mul_of_le (continuousOn_kernel ha hR hs)
      (continuous_expneg _).continuousOn Ioc_subset_Ioi_self measurableSet_Ioc (g := fun _ => 1)
      this (fun u hu => by
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (sq_nonneg _) hu.1.le)).const_mul _
  have e : ∫ u in Ioc 0 u₀, (∑ k ∈ Finset.Ico 1 k₀, c k * ((rexp (-((k : ℝ) ^ 2 * u)) : ℂ) *
      kernel a s u)) = ∑ k ∈ Finset.Ico 1 k₀, ∫ u in Ioc 0 u₀, c k *
        ((rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * kernel a s u) :=
    integral_finsetSum _ fun k _ => hL k
  unfold mainTermOdd lowerL
  calc ∫ u in Ioc 0 u₀, (-∑ k ∈ Finset.Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) *
        kernel a s u
      = ∫ u in Ioc 0 u₀, -(∑ k ∈ Finset.Ico 1 k₀, c k * ((rexp (-((k : ℝ) ^ 2 * u)) : ℂ) *
          kernel a s u)) := by
        congr 1; funext u; rw [neg_mul, Finset.sum_mul]
        congr 1; exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [integral_neg, e]
        simp_rw [integral_const_mul]

/-- The odd twisted right-hand side with `L_k(s+1)` as entire series. -/
noncomputable def twistedOddRHS' (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (q : ℕ) (χ : ℤ → ℂ) (s : ℂ) : ℂ :=
  (∑' k : ℕ, χ ((k + k₀ : ℕ) : ℤ) * ((k + k₀ : ℕ) : ℂ) * kTerm (kernel a (s + 1)) u₀ (k + k₀)) +
    (∑' m : ℕ, charDualOdd q χ (m + 1) *
      dualTermOdd (kernel a (s + 1)) u₀ (π ^ 2 / q ^ 2) (m + 1)) -
    ∑ k ∈ Finset.Ico 1 k₀, χ k * k * (∑' n, lSeriesTerm a u₀ k n (s + 1))

/-- **Odd periodic weights**: `L_F^{≥k₀}(s, χ)` extends to an entire function of `s`, given by the
twisted splitting. -/
theorem zetaTail_char_odd_entire (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {q : ℕ} (hq : 0 < q)
    {χ : ℤ → ℂ} (hper : Function.Periodic χ q) (hodd : ∀ k, χ (-k) = -χ k) {u₀ : ℝ}
    (hu₀ : 0 < u₀) :
    Differentiable ℂ (twistedOddRHS' a k₀ u₀ q χ) ∧
      ∀ s : ℂ, 2 < s.re → twistedOddRHS' a k₀ u₀ q χ s = zetaTail (fun k => χ k * F k) k₀ s := by
  set Bχ := ∑ a ∈ range q, ‖χ a‖
  have hB0 : 0 ≤ Bχ := sum_nonneg fun _ _ => norm_nonneg _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · have hk := differentiable_sum_kTerm_weighted ha hR hRk hu₀ (w := fun k : ℕ => χ k * k)
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
    have hL : Differentiable ℂ fun s => ∑ k ∈ Finset.Ico 1 k₀, χ k * k *
        (∑' n, lSeriesTerm a u₀ k n (s + 1)) :=
      Differentiable.fun_sum fun k hk =>
        ((differentiable_lSeries ha hR hu₀ (Finset.mem_Ico.1 hk).1).comp
          (differentiable_id.add_const 1)).const_mul _
    exact (hk.add hd).sub hL
  · intro s hs
    have hs1 : 1 < (s + 1).re := by simp; linarith
    rw [zetaTail_split_char_odd ha hR hk₀ hRk hF hs hq hper hodd hu₀, twistedOddRHS',
      mainTermOdd_eq_sum ha hR hu₀ _ k₀ (by linarith), sub_eq_add_neg]
    congr 2
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [(hasSum_lSeries ha hR hu₀ (Finset.mem_Ico.1 hk).1 hs1).tsum_eq]

end ZetaF
