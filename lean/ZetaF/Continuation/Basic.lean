/-
# Tools for the analytic continuation

* `differentiable_tsum_of_local_bound`: a series of entire functions is entire if, near every point, all
  but finitely many terms are bounded by a summable sequence.
* Mellin-type integrals over `(u₀, ∞)` and `(0, u₀]` are entire functions of the exponent.
-/
import ZetaF.GammaUniform
import ZetaF.Holonomic.DualMoments
import ZetaF.Splitting.Kernel

open MeasureTheory Set Filter Finset Asymptotics
open scoped Real Topology

namespace ZetaF

/-- A series of entire functions is entire if, near every point `s₀`, all terms with `n ≥ N` are
bounded by a summable sequence. -/
theorem differentiable_tsum_of_local_bound {T : ℕ → ℂ → ℂ} (hT : ∀ n, Differentiable ℂ (T n))
    (hb : ∀ s₀ : ℂ, ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧
      ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1, ‖T n s‖ ≤ b n) :
    Differentiable ℂ fun s => ∑' n, T n s := by
  intro s₀
  obtain ⟨N, b, hbs, hbn⟩ := hb s₀
  have hfin : ∀ n, ∃ B, ∀ s ∈ Metric.closedBall s₀ 1, ‖T n s‖ ≤ B := fun n =>
    (isCompact_closedBall s₀ 1).exists_bound_of_continuousOn (hT n).continuous.continuousOn
  choose B hB using hfin
  set u : ℕ → ℝ := fun n => if n < N then B n else b n
  have hu : Summable u := by
    have h1 : Summable fun n : ℕ => if n < N then B n - b n else 0 :=
      summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
        simp only [Finset.mem_range] at hn; simp [hn]
    refine (hbs.add h1).congr fun n => ?_
    simp only [u]; split_ifs <;> ring
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu (fun n => (hT n).differentiableOn)
    Metric.isOpen_ball (fun n s hs => by
      simp only [u]
      split_ifs with h
      · exact hB n s (Metric.ball_subset_closedBall hs)
      · exact hbn n (by omega) s hs)
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

/-! ### Mellin transforms of indicators -/

lemma mellin_indicator {g : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0) (w : ℂ) :
    mellin (S.indicator g) w = ∫ t in S, (t : ℂ) ^ (w - 1) * g t := by
  unfold mellin
  have e : ∀ t : ℝ, (t : ℂ) ^ (w - 1) • S.indicator g t =
      S.indicator (fun t => (t : ℂ) ^ (w - 1) * g t) t := by
    intro t; by_cases ht : t ∈ S <;> simp [ht]
  simp_rw [e]
  rw [setIntegral_indicator hS, inter_eq_right.2 hS0]

lemma integrableOn_of_mellinConvergent_indicator {g : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) {w : ℂ} (h : MellinConvergent (S.indicator g) w) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * g t) S := by
  unfold MellinConvergent at h
  have e : (fun t : ℝ => (t : ℂ) ^ (w - 1) • S.indicator g t) =
      S.indicator (fun t => (t : ℂ) ^ (w - 1) * g t) := by
    funext t; by_cases ht : t ∈ S <;> simp [ht]
  rw [e, IntegrableOn, integrable_indicator_iff hS, IntegrableOn, Measure.restrict_restrict hS,
    inter_eq_left.2 hS0] at h
  exact h

/-! ### `U(w) = ∫_{u₀}^∞ e^{-κu} u^{w-1} du` -/

/-- `∫_{u₀}^∞ u^{w-1} e^{-κu} du`, an entire function of `w` (for `κ, u₀ > 0`). -/
noncomputable def upperLaplace (κ u₀ : ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioi u₀, (u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)

section upperLaplace

variable {κ u₀ : ℝ} (hκ : 0 < κ) (hu₀ : 0 < u₀)
include hκ hu₀

lemma upperLaplace_isBigO (w : ℂ) :
    let f := (Ioi u₀).indicator fun u : ℝ => (rexp (-(κ * u)) : ℂ)
    LocallyIntegrableOn f (Ioi 0) ∧ (f =O[atTop] fun x => x ^ (-(w.re + 1))) ∧
      (f =O[𝓝[>] 0] fun x => x ^ (-(w.re - 1))) := by
  intro f
  have hint : Integrable f := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    have := (exp_neg_integrableOn_Ioi u₀ hκ).ofReal (𝕜 := ℂ)
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [neg_mul]
  refine ⟨(hint.integrableOn (s := Ioi 0)).locallyIntegrableOn, ?_, ?_⟩
  · have h1 : f =O[atTop] fun x : ℝ => Real.exp (-κ * x) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
      simp only [f, Set.indicator_apply, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      split_ifs
      · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul]
      · simp; positivity
    exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hκ _).isBigO
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT hu₀] with x hx
    simp [f, Set.indicator_apply, not_lt.2 hx.2.le]

theorem differentiable_upperLaplace : Differentiable ℂ (upperLaplace κ u₀) := by
  intro w
  obtain ⟨h1, h2, h3⟩ := upperLaplace_isBigO hκ hu₀ w
  have hd := mellin_differentiableAt_of_isBigO_rpow h1 h2 (by linarith) h3 (by linarith)
  have e : mellin ((Ioi u₀).indicator fun u : ℝ => (rexp (-(κ * u)) : ℂ)) = upperLaplace κ u₀ := by
    funext v; rw [mellin_indicator measurableSet_Ioi (Ioi_subset_Ioi hu₀.le)]; rfl
  rwa [e] at hd

theorem integrableOn_upperLaplace (w : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)) (Ioi u₀) := by
  obtain ⟨h1, h2, h3⟩ := upperLaplace_isBigO hκ hu₀ w
  exact integrableOn_of_mellinConvergent_indicator measurableSet_Ioi (Ioi_subset_Ioi hu₀.le)
    (mellinConvergent_of_isBigO_rpow h1 h2 (by linarith) h3 (by linarith))

lemma integral_norm_upperLaplace_le {w : ℂ} (hw : 0 < w.re) :
    ∫ u in Ioi u₀, ‖(u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)‖ ≤
      Real.Gamma w.re * (1 / κ) ^ w.re := by
  have e : ∀ u ∈ Ioi (0 : ℝ), ‖(u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)‖ =
      u ^ (w.re - 1) * rexp (-(κ * u)) := by
    intro u hu
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]; simp
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => e u (lt_trans hu₀ hu))]
  calc ∫ u in Ioi u₀, u ^ (w.re - 1) * rexp (-(κ * u))
      ≤ ∫ u in Ioi 0, u ^ (w.re - 1) * rexp (-(κ * u)) := by
        apply setIntegral_mono_set (integrableOn_rpow_mul_exp hw hκ)
        · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
          exact mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (Real.exp_pos _).le
        · exact Eventually.of_forall (Ioi_subset_Ioi hu₀.le)
    _ = _ := by rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hw hκ, mul_comm]

lemma norm_upperLaplace_le {w : ℂ} (hw : 0 < w.re) :
    ‖upperLaplace κ u₀ w‖ ≤ Real.Gamma w.re * (1 / κ) ^ w.re :=
  (norm_integral_le_integral_norm _).trans (integral_norm_upperLaplace_le hκ hu₀ hw)

end upperLaplace

/-! ### `V(w) = ∫₀^{u₀} u^{-1/2} e^{-c/u} u^{w-1} du` -/

/-- `∫₀^{u₀} u^{w-1} u^{-1/2} e^{-c/u} du` (this is `D_{w-1/2}(c)` in the paper's notation), an entire
function of `w` for `c, u₀ > 0`. -/
noncomputable def lowerDual (c u₀ : ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioc 0 u₀, (u : ℂ) ^ (w - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)

lemma rpow_neg_half_mul_exp_eq {c u : ℝ} (hu : 0 < u) :
    u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) = ‖dualWeight c (1 / 2) u‖ := by
  rw [norm_dualWeight_of_pos hu, Real.rpow_neg hu.le, Real.inv_rpow hu.le]
  simp [div_eq_mul_inv]

/-- A bound for `u^{-1/2} e^{-c/u}` on `(0, u₀]`, uniform in `c ≥ c₁`. -/
lemma exists_bound_rpow_neg_half_mul_exp {c₁ : ℝ} (hc₁ : 0 < c₁) (u₀ : ℝ) :
    ∃ S, 0 ≤ S ∧ ∀ c, c₁ ≤ c → ∀ u ∈ Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) ≤ S := by
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := u₀)).exists_bound_of_continuousOn
    (continuous_dualWeight hc₁ (1 / 2)).continuousOn
  refine ⟨max S 0, le_max_right _ _, fun c hc u hu => ?_⟩
  rw [rpow_neg_half_mul_exp_eq hu.1]
  exact (norm_dualWeight_anti hc).trans ((hS u ⟨hu.1.le, hu.2⟩).trans (le_max_left _ _))

lemma continuousOn_rpow_neg_half_mul_exp (c : ℝ) :
    ContinuousOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u))) (Ioi 0) :=
  continuousOn_dualWeight c |>.congr fun u _ => by ring_nf

section lowerDual

variable {c u₀ : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀)
include hc hu₀

lemma lowerDual_isBigO (w : ℂ) :
    let f := (Ioc 0 u₀).indicator fun u : ℝ => ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)
    LocallyIntegrableOn f (Ioi 0) ∧ (f =O[atTop] fun x => x ^ (-(w.re + 1))) ∧
      (f =O[𝓝[>] 0] fun x => x ^ (-(w.re - 1))) := by
  intro f
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  have hint : Integrable f := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    refine Integrable.mono' (integrableOn_const (C := S) (by simp) (by simp)) ?_ ?_
    · exact (Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_rpow_neg_half_mul_exp c).mono Ioc_subset_Ioi_self)).aestronglyMeasurable
        measurableSet_Ioc
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _)
        (Real.exp_pos _).le)]
      exact hS c le_rfl u hu
  refine ⟨(hint.integrableOn (s := Ioi 0)).locallyIntegrableOn, ?_, ?_⟩
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop u₀] with x hx
    simp [f, Set.indicator_apply, not_le.2 hx]
  · have ht := tendsto_dualWeight_zero hc ((1 / 2 : ℂ) - (w.re - 1 : ℝ))
    have ht' := (ht.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).norm
    rw [norm_zero] at ht'
    refine IsBigO.of_bound 1 ?_
    filter_upwards [ht'.eventually (ge_mem_nhds one_pos), self_mem_nhdsWithin] with x h1 hx
    have hx : 0 < x := hx
    simp only [f, Set.indicator_apply]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _)
        (Real.exp_pos _).le), one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
      rw [norm_dualWeight_of_pos hx] at h1
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re] at h1
      rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le] at h1
      have e : x ^ (-(1 / 2 : ℝ)) = x ^ (-(w.re - 1)) * x ^ (-(1 / 2 - (w.re - 1))) := by
        rw [← Real.rpow_add hx]; ring_nf
      rw [e, mul_assoc]
      apply mul_le_of_le_one_right (Real.rpow_nonneg hx.le _)
      convert h1 using 2; ring_nf
    · simp

theorem differentiable_lowerDual : Differentiable ℂ (lowerDual c u₀) := by
  intro w
  obtain ⟨h1, h2, h3⟩ := lowerDual_isBigO hc hu₀ w
  have hd := mellin_differentiableAt_of_isBigO_rpow h1 h2 (by linarith) h3 (by linarith)
  have e : mellin ((Ioc 0 u₀).indicator fun u : ℝ =>
      ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)) = lowerDual c u₀ := by
    funext v; rw [mellin_indicator measurableSet_Ioc Ioc_subset_Ioi_self]; rfl
  rwa [e] at hd

theorem integrableOn_lowerDual (w : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (w - 1) *
      ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)) (Ioc 0 u₀) := by
  obtain ⟨h1, h2, h3⟩ := lowerDual_isBigO hc hu₀ w
  exact integrableOn_of_mellinConvergent_indicator measurableSet_Ioc Ioc_subset_Ioi_self
    (mellinConvergent_of_isBigO_rpow h1 h2 (by linarith) h3 (by linarith))

end lowerDual

lemma integral_norm_lowerDual_le {c u₀ S : ℝ} (hu₀ : 0 < u₀) {w : ℂ} (hw : 0 < w.re)
    (hS : ∀ u ∈ Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) ≤ S) :
    ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ (w - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖ ≤
      S * (u₀ ^ w.re / w.re) := by
  have hint : IntegrableOn (fun u : ℝ => u ^ (w.re - 1)) (Ioc 0 u₀) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  calc _ ≤ ∫ u in Ioc 0 u₀, S * u ^ (w.re - 1) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hint.const_mul S) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)]
        simp only [Complex.sub_re, Complex.one_re]
        rw [mul_comm S]
        exact mul_le_mul_of_nonneg_left (hS u hu) (Real.rpow_nonneg hu.1.le _)
    _ = S * (u₀ ^ w.re / w.re) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hu₀.le,
          integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
        simp

end ZetaF
