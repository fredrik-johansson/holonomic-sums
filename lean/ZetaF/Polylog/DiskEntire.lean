/-
# Theorem 4.1(1) inside the disc, for all `s`

For complex `c` with `Re c > 0` the dual integrals `J^{(δ)}_s(c)` are entire in `s`: they are the
series `∑ a_n/Γ((s+n)/2) · D(c)` of entire functions, and since `|e^{-c/u}| = e^{-Re c/u}` every
estimate reduces to the real case with `c` replaced by `Re c`.  For `α` in the upper diamond the
right-hand side of the splitting (with `H`, `L_k` given by their termwise series) is therefore
entire in `s`, as is `Li_F^{≥k₀}(s, z)` itself (`|z| < 1`), and the identity of
`polylogTail_split_disk` extends from `Re s > 2` to all `s` (`polylogTail_split_disk_all`).
-/
import ZetaF.Polylog.Disk

open MeasureTheory Set Filter Metric Asymptotics
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-! ### `D(c) = ∫₀^{u₀} u^{w-1} u^{-1/2} e^{-c/u} du` for complex `c` -/

/-- The weight `u^{-1/2} e^{-c/u}` for complex `c`. -/
noncomputable def dualWC (c : ℂ) (u : ℝ) : ℂ := ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(c / u))

/-- `∫₀^{u₀} u^{w-1} u^{-1/2} e^{-c/u} du`. -/
noncomputable def lowerDualC (c : ℂ) (u₀ : ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioc 0 u₀, (u : ℂ) ^ (w - 1) * dualWC c u

lemma norm_dualWC {c : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖dualWC c u‖ = ‖(((u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u))) : ℝ) : ℂ)‖ := by
  rw [dualWC, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_exp,
    Real.norm_of_nonneg (Real.rpow_nonneg hu.le _),
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)]
  simp only [Complex.neg_re, Complex.div_ofReal_re]

lemma norm_cpow_mul_dualWC {c : ℂ} {u : ℝ} (hu : 0 < u) (v : ℂ) :
    ‖(u : ℂ) ^ v * dualWC c u‖ =
      ‖(u : ℂ) ^ v * (((u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u))) : ℝ) : ℂ)‖ := by
  rw [norm_mul, norm_mul, norm_dualWC hu]

lemma continuousOn_cpow_mul_dualWC (c v : ℂ) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ v * dualWC c u) (Ioi 0) := by
  have h := continuousOn_geoJC_integrand (h := fun u : ℝ => (u : ℂ) ^ v) (fun u hu =>
    (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 hu)).continuousWithinAt) (1 / 2) c
  exact h.congr fun u _ => by simp only [dualWC]; ring

lemma integrableOn_lowerDualC {c : ℂ} (hc : 0 < c.re) {u₀ : ℝ} (hu₀ : 0 < u₀) (w : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (w - 1) * dualWC c u) (Ioc 0 u₀) := by
  refine Integrable.mono' (integrableOn_lowerDual hc hu₀ w).norm
    ((continuousOn_cpow_mul_dualWC c _).mono Ioc_subset_Ioi_self |>.aestronglyMeasurable
      measurableSet_Ioc) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
  exact (norm_cpow_mul_dualWC hu.1 _).le

theorem differentiable_lowerDualC {c : ℂ} (hc : 0 < c.re) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Differentiable ℂ (lowerDualC c u₀) := by
  intro w
  obtain ⟨h1, h2, h3⟩ := lowerDual_isBigO hc hu₀ w
  set f := (Ioc 0 u₀).indicator fun u : ℝ => dualWC c u
  set fr := (Ioc 0 u₀).indicator fun u : ℝ =>
    (((u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u))) : ℝ) : ℂ)
  have hle : ∀ x, ‖f x‖ ≤ ‖fr x‖ := fun x => by
    simp only [f, fr, Set.indicator_apply]
    split_ifs with hx
    · exact (norm_dualWC hx.1).le
    · simp
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  have hint : Integrable f := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    refine Integrable.mono' (integrableOn_const (C := S) (by simp) (by simp)) ?_ ?_
    · have := (continuousOn_cpow_mul_dualWC c 0).mono (show Ioc (0 : ℝ) u₀ ⊆ Ioi 0 from Ioc_subset_Ioi_self)
      refine (this.congr fun u _ => ?_).aestronglyMeasurable measurableSet_Ioc
      simp [Complex.cpow_zero]
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
      rw [norm_dualWC hu.1, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg
        (Real.rpow_nonneg hu.1.le _) (Real.exp_pos _).le)]
      exact hS _ le_rfl u hu
  have hd := mellin_differentiableAt_of_isBigO_rpow
    ((hint.integrableOn (s := Ioi 0)).locallyIntegrableOn)
    ((isBigO_of_le _ hle).trans h2) (by linarith) ((isBigO_of_le _ hle).trans h3) (by linarith)
  have e : mellin f = lowerDualC c u₀ := by
    funext v; rw [mellin_indicator measurableSet_Ioc Ioc_subset_Ioi_self]; rfl
  rwa [e] at hd

/-! ### The series for `J^{(0)}_s(c)` and `J^{(1)}_{s+1}(c)` -/

noncomputable def dSeriesTermC (a : ℕ → ℂ) (c : ℂ) (u₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  a n * (Complex.Gamma ((s + n) / 2))⁻¹ * lowerDualC c u₀ ((s + n) / 2)

noncomputable def dSeriesTermOddC (a : ℕ → ℂ) (c : ℂ) (u₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹ * lowerDualC c u₀ ((s + 1 + n) / 2 - 1)

lemma differentiable_dSeriesTermC {c : ℂ} (hc : 0 < c.re) {u₀ : ℝ} (hu₀ : 0 < u₀) (n : ℕ) :
    Differentiable ℂ (dSeriesTermC a c u₀ n) :=
  ((differentiable_const _).mul (Complex.differentiable_one_div_Gamma.comp
    (differentiable_half_shift n))).mul ((differentiable_lowerDualC hc hu₀).comp
      (differentiable_half_shift n))

lemma differentiable_dSeriesTermOddC {c : ℂ} (hc : 0 < c.re) {u₀ : ℝ} (hu₀ : 0 < u₀) (n : ℕ) :
    Differentiable ℂ (dSeriesTermOddC a c u₀ n) := by
  have hw : Differentiable ℂ fun s : ℂ => (s + 1 + n) / 2 := by fun_prop
  exact ((differentiable_const _).mul (Complex.differentiable_one_div_Gamma.comp hw)).mul
    ((differentiable_lowerDualC hc hu₀).comp (hw.sub_const 1))

lemma integral_norm_cpow_dualWC {c : ℂ} {u₀ : ℝ} (v : ℂ) :
    ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ v * dualWC c u‖ =
      ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ v * (((u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u))) : ℝ) : ℂ)‖ :=
  setIntegral_congr_fun measurableSet_Ioc fun _ hu => norm_cpow_mul_dualWC hu.1 v

/-- `J^{(0)}_s(c) = ∑_n a_n/Γ((s+n)/2) D_{(s+n-1)/2}(c)` for complex `c`, every `s`. -/
theorem hasSum_dSeriesC (ha : GeomBounded a R) (hR : 0 ≤ R) {c : ℂ} (hc : 0 < c.re) {u₀ : ℝ}
    (hu₀ : 0 < u₀) (s : ℂ) :
    HasSum (fun n => dSeriesTermC a c u₀ n s) (geoJC (kernel a s) u₀ (1 / 2) c) := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s
  have e : ∀ n (u : ℝ), dualWC c u * kernelTerm a s n u =
      (a n * (Complex.Gamma ((s + n) / 2))⁻¹) * ((u : ℂ) ^ ((s + n) / 2 - 1) * dualWC c u) := by
    intro n u; unfold kernelTerm; ring
  have hint : ∀ n, IntegrableOn (fun u => dualWC c u * kernelTerm a s n u) (Ioc 0 u₀) :=
    fun n => by simp_rw [e]; exact (integrableOn_lowerDualC hc hu₀ _).const_mul _
  have hnorm : ∀ n, ∫ u in Ioc 0 u₀, ‖dualWC c u * kernelTerm a s n u‖ =
      ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀,
        ‖(u : ℂ) ^ ((s + n) / 2 - 1) * (((u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u))) : ℝ) : ℂ)‖ :=
    fun n => by
      simp_rw [e, norm_mul]
      rw [integral_const_mul]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      rw [norm_dualWC hu.1]
  have hsum : Summable fun n => ∫ u in Ioc 0 u₀, ‖dualWC c u * kernelTerm a s n u‖ := by
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_nat_add_iff N).2 hb)
    rw [hnorm]; exact hbn (n + N) (Nat.le_add_left _ _) s (Metric.mem_ball_self one_pos)
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext n; simp_rw [e]; rw [integral_const_mul]; rfl
  · unfold geoJC
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [kernel, dualWC]
    rw [← tsum_mul_left]

lemma weight_odd_eqC {c : ℂ} {u : ℝ} (hu : 0 < u) (w : ℂ) :
    ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(c / u)) * (u : ℂ) ^ (w - 1) =
      (u : ℂ) ^ (w - 1 - 1) * dualWC c u := by
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  have h32 : u ^ (-(3 / 2 : ℝ)) = u ^ (-(1 / 2 : ℝ)) * u⁻¹ := by
    rw [show -(3 / 2 : ℝ) = -(1 / 2) + -1 by norm_num, Real.rpow_add hu, Real.rpow_neg_one]
  have hw : (u : ℂ) ^ (w - 1 - 1) = (u : ℂ) ^ (w - 1) * (u : ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hu', Complex.cpow_one, div_eq_mul_inv]
  rw [h32, hw, dualWC]
  push_cast
  ring

/-- `J^{(1)}_{s+1}(c)` as a series, for complex `c` and every `s`. -/
theorem hasSum_dSeriesOddC (ha : GeomBounded a R) (hR : 0 ≤ R) {c : ℂ} (hc : 0 < c.re) {u₀ : ℝ}
    (hu₀ : 0 < u₀) (s : ℂ) :
    HasSum (fun n => dSeriesTermOddC a c u₀ n s) (geoJC (kernel a (s + 1)) u₀ (3 / 2) c) := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeriesOdd_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s
  have e : ∀ n, ∀ u ∈ Ioc (0 : ℝ) u₀,
      ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(c / u)) * kernelTerm a (s + 1) n u =
      (a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹) *
        ((u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) * dualWC c u) := by
    intro n u hu
    unfold kernelTerm
    rw [← weight_odd_eqC hu.1]; ring
  have hint : ∀ n, IntegrableOn (fun u => ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(c / u)) * kernelTerm a (s + 1) n u) (Ioc 0 u₀) := fun n => by
    have h1 : IntegrableOn (fun u : ℝ => (a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹) *
        ((u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) * dualWC c u)) (Ioc 0 u₀) :=
      (integrableOn_lowerDualC hc hu₀ _).const_mul _
    exact h1.congr_fun (fun u hu => (e n u hu).symm) measurableSet_Ioc
  have hnorm : ∀ n, ∫ u in Ioc 0 u₀, ‖((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(c / u)) * kernelTerm a (s + 1) n u‖ =
      ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀,
        ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
          (((u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u))) : ℝ) : ℂ)‖ := fun n => by
    rw [← integral_norm_cpow_dualWC, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [e n u hu, norm_mul, norm_mul]
  have hsum : Summable fun n => ∫ u in Ioc 0 u₀, ‖((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(c / u)) * kernelTerm a (s + 1) n u‖ := by
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_nat_add_iff N).2 hb)
    rw [hnorm]; exact hbn (n + N) (Nat.le_add_left _ _) s (Metric.mem_ball_self one_pos)
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext n
    rw [setIntegral_congr_fun measurableSet_Ioc (e n), integral_const_mul]; rfl
  · unfold geoJC
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [kernel]
    rw [← tsum_mul_left]

/-! ### Locally uniform bounds -/

theorem dualJC_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ c : ℂ, c₁ ≤ c.re →
      ‖geoJC (kernel a s) u₀ (1 / 2) c‖ ≤
        rexp (-((c.re - c₁) / u₀)) * B := by
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
  have hc0 : 0 < c.re := lt_of_lt_of_le hc₁ hc
  have hsum := hasSum_dSeriesC ha hR hc0 hu₀ s
  set E := rexp (-((c.re - c₁) / u₀))
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖dSeriesTermC a c u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)) : ℝ) : ℂ)‖) := by
    unfold dSeriesTermC lowerDualC
    rw [norm_mul, norm_mul, mul_left_comm, ← integral_const_mul]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by positivity)
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((integrableOn_lowerDual hc₁ hu₀ _).norm.const_mul E) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    dsimp only
    rw [norm_cpow_mul_dualWC hu.1]
    have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hr (Real.exp_pos _).le),
      Real.norm_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
    have hexp : rexp (-(c.re / u)) ≤ E * rexp (-(c₁ / u)) := by
      simp only [E]
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : (c.re - c₁) / u₀ ≤ (c.re - c₁) / u :=
        div_le_div_of_nonneg_left (by linarith) hu.1 hu.2
      have e : c.re / u = (c.re - c₁) / u + c₁ / u := by ring
      rw [e]; linarith
    set P := ‖(u : ℂ) ^ ((s + n) / 2 - 1)‖
    have hP : 0 ≤ P := norm_nonneg _
    calc P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u)))
        = (u ^ (-(1 / 2 : ℝ)) * P) * rexp (-(c.re / u)) := by ring
      _ ≤ (u ^ (-(1 / 2 : ℝ)) * P) * (E * rexp (-(c₁ / u))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hr hP)
      _ = E * (P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)))) := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs

theorem dualJOddC_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (s₀ : ℂ) :
    ∃ B, ∀ s ∈ Metric.ball s₀ 1, ∀ c : ℂ, c₁ ≤ c.re →
      ‖geoJC (kernel a (s + 1)) u₀ (3 / 2) c‖ ≤
        rexp (-((c.re - c₁) / u₀)) * B := by
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
  have hc0 : 0 < c.re := lt_of_lt_of_le hc₁ hc
  have hsum := hasSum_dSeriesOddC ha hR hc0 hu₀ s
  set E := rexp (-((c.re - c₁) / u₀))
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded (hg.hasSum.mul_left E) fun n => ?_
  have hterm : ‖dSeriesTermOddC a c u₀ n s‖ ≤ E * (‖a n‖ *
      ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1) *
        ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)) : ℝ) : ℂ)‖) := by
    unfold dSeriesTermOddC lowerDualC
    rw [norm_mul, norm_mul, mul_left_comm, ← integral_const_mul]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by positivity)
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((integrableOn_lowerDual hc₁ hu₀ _).norm.const_mul E) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    dsimp only
    rw [norm_cpow_mul_dualWC hu.1]
    have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hr (Real.exp_pos _).le),
      Real.norm_of_nonneg (mul_nonneg hr (Real.exp_pos _).le)]
    have hexp : rexp (-(c.re / u)) ≤ E * rexp (-(c₁ / u)) := by
      simp only [E]
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : (c.re - c₁) / u₀ ≤ (c.re - c₁) / u :=
        div_le_div_of_nonneg_left (by linarith) hu.1 hu.2
      have e : c.re / u = (c.re - c₁) / u + c₁ / u := by ring
      rw [e]; linarith
    set P := ‖(u : ℂ) ^ ((s + 1 + n) / 2 - 1 - 1)‖
    have hP : 0 ≤ P := norm_nonneg _
    calc P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c.re / u)))
        = (u ^ (-(1 / 2 : ℝ)) * P) * rexp (-(c.re / u)) := by ring
      _ ≤ (u ^ (-(1 / 2 : ℝ)) * P) * (E * rexp (-(c₁ / u))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hr hP)
      _ = E * (P * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c₁ / u)))) := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  simp only [g]
  split_ifs with h
  · exact hG n s hs
  · exact hbn n (by omega) s hs

/-! ### Everything is entire in `s` -/

lemma differentiable_geoJC_half (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {c : ℂ} (hc : 0 < c.re) : Differentiable ℂ fun s => geoJC (kernel a s) u₀ (1 / 2) c := by
  have e : (fun s => geoJC (kernel a s) u₀ (1 / 2) c) = fun s => ∑' n, dSeriesTermC a c u₀ n s :=
    funext fun s => ((hasSum_dSeriesC ha hR hc hu₀ s).tsum_eq).symm
  rw [e]
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  refine differentiable_tsum_of_local_bound (fun n => differentiable_dSeriesTermC hc hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  refine ⟨N, b, hb, fun n hn s hs => le_trans ?_ (hbn n hn s hs)⟩
  unfold dSeriesTermC lowerDualC
  rw [norm_mul, norm_mul, ← integral_norm_cpow_dualWC]
  gcongr
  exact norm_integral_le_integral_norm _

lemma differentiable_geoJC_three_half (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ}
    (hu₀ : 0 < u₀) {c : ℂ} (hc : 0 < c.re) :
    Differentiable ℂ fun s => geoJC (kernel a (s + 1)) u₀ (3 / 2) c := by
  have e : (fun s => geoJC (kernel a (s + 1)) u₀ (3 / 2) c) =
      fun s => ∑' n, dSeriesTermOddC a c u₀ n s :=
    funext fun s => ((hasSum_dSeriesOddC ha hR hc hu₀ s).tsum_eq).symm
  rw [e]
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  refine differentiable_tsum_of_local_bound (fun n => differentiable_dSeriesTermOddC hc hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := dSeriesOdd_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  refine ⟨N, b, hb, fun n hn s hs => le_trans ?_ (hbn n hn s hs)⟩
  unfold dSeriesTermOddC lowerDualC
  rw [norm_mul, norm_mul, ← integral_norm_cpow_dualWC]
  gcongr
  exact norm_integral_le_integral_norm _

lemma differentiable_dualTermC_s (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {α : ℂ} (hα : 0 < margin α) (n : ℤ) : Differentiable ℂ fun s => dualTermC a u₀ s α n := by
  have hc := geoDualC_re_pos hα n
  unfold dualTermC
  exact (differentiable_geoJC_half ha hR hu₀ hc).sub
    ((differentiable_const _).mul (differentiable_geoJC_three_half ha hR hu₀ hc))

lemma margin_le_geoDualC_re {α : ℂ} (hα : 0 < margin α) (n : ℤ) :
    π ^ 2 * margin α ^ 2 ≤ (geoDualC α n).re := by
  obtain ⟨h0, h1⟩ := re_mem_of_margin_pos hα
  have hd := min_le_abs_int_sub h0 h1 n
  have hm : margin α ≤ min α.re (1 - α.re) := by unfold margin; linarith [abs_nonneg α.im]
  have := geoDualC_re_ge hα n
  have hπ : 0 < π ^ 2 := by positivity
  calc π ^ 2 * margin α ^ 2 = π ^ 2 * margin α * margin α := by ring
    _ ≤ π ^ 2 * margin α * |(n : ℝ) - α.re| :=
        mul_le_mul_of_nonneg_left (hm.trans hd) (by positivity)
    _ ≤ _ := this

/-- **The dual sum is entire in `s`**, for `α` in the diamond. -/
theorem differentiable_dualSum_s (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {α : ℂ} (hα : 0 < margin α) : Differentiable ℂ fun s => ∑' n : ℤ, dualTermC a u₀ s α n := by
  intro s₀
  set δ := margin α
  set c₁ := π ^ 2 * δ ^ 2
  have hc₁ : 0 < c₁ := by positivity
  obtain ⟨B₀, hB₀⟩ := dualJC_local_bound ha hR hu₀ hc₁ s₀ (a := a)
  obtain ⟨B₁, hB₁⟩ := dualJOddC_local_bound ha hR hu₀ hc₁ s₀ (a := a)
  have hc0 := margin_le_geoDualC_re hα 0
  have hB₀0 : 0 ≤ B₀ := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1
    ((norm_nonneg _).trans (hB₀ s₀ (mem_ball_self one_pos) _ hc0))
  have hB₁0 : 0 ≤ B₁ := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1
    ((norm_nonneg _).trans (hB₁ s₀ (mem_ball_self one_pos) _ hc0))
  set l := π ^ 2 * δ / u₀
  have hl : 0 < l := by positivity
  have hbound : ∀ n : ℤ, ∀ s ∈ ball s₀ 1, ‖dualTermC a u₀ s α n‖ ≤
      rexp (c₁ / u₀) * (rexp (-(l * (|(n : ℝ)| - 1))) * ((B₀ + 2 * π * B₁) + π * B₁ * |(n : ℝ)|)) := by
    intro n s hs
    have hcn := margin_le_geoDualC_re hα n
    have hE : rexp (-(((geoDualC α n).re - c₁) / u₀)) ≤
        rexp (c₁ / u₀) * rexp (-(l * (|(n : ℝ)| - 1))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 := geoDualC_re_ge hα n
      have h2 := abs_int_sub_ge hα n
      have hδ : 0 < δ := hα
      have : π ^ 2 * δ * (|(n : ℝ)| - 1) ≤ (geoDualC α n).re := by
        have hπ : 0 < π ^ 2 * δ := by positivity
        nlinarith
      have e : l * (|(n : ℝ)| - 1) = π ^ 2 * δ * (|(n : ℝ)| - 1) / u₀ := by
        simp only [l]; ring
      rw [e, sub_div]
      have := div_le_div_of_nonneg_right this hu₀.le
      linarith
    have hnα : ‖(n : ℂ) - α‖ ≤ |(n : ℝ)| + 2 := by
      obtain ⟨h0, h1⟩ := re_mem_of_margin_pos hα
      have him : |α.im| < 1 := by
        have hm' : 0 < min α.re (1 - α.re) - |α.im| := hα
        linarith [min_le_left α.re (1 - α.re)]
      calc ‖(n : ℂ) - α‖ ≤ ‖(n : ℂ)‖ + ‖α‖ := norm_sub_le _ _
        _ ≤ |(n : ℝ)| + (|α.re| + |α.im|) := by
            gcongr
            · rw [Complex.norm_intCast]
            · exact Complex.norm_le_abs_re_add_abs_im α
        _ ≤ |(n : ℝ)| + 2 := by rw [abs_of_pos h0]; linarith
    set E := rexp (-(((geoDualC α n).re - c₁) / u₀))
    have hJ0 := hB₀ s hs _ hcn
    have hJ1 := hB₁ s hs _ hcn
    unfold dualTermC
    calc _ ≤ ‖geoJC (kernel a s) u₀ (1 / 2) (geoDualC α n)‖ +
          ‖Complex.I * π * ((n : ℂ) - α)‖ *
            ‖geoJC (kernel a (s + 1)) u₀ (3 / 2) (geoDualC α n)‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      _ ≤ E * B₀ + (π * (|(n : ℝ)| + 2)) * (E * B₁) := by
          gcongr
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_of_nonneg Real.pi_pos.le]
          exact mul_le_mul_of_nonneg_left hnα Real.pi_pos.le
      _ = E * ((B₀ + 2 * π * B₁) + π * B₁ * |(n : ℝ)|) := by ring
      _ ≤ (rexp (c₁ / u₀) * rexp (-(l * (|(n : ℝ)| - 1)))) *
            ((B₀ + 2 * π * B₁) + π * B₁ * |(n : ℝ)|) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
      _ = _ := by ring
  have hd : DifferentiableOn ℂ (fun s => ∑' n : ℤ, dualTermC a u₀ s α n) (ball s₀ 1) :=
    Complex.differentiableOn_tsum_of_summable_norm
      ((summable_int_exp_abs hl _ _).mul_left _)
      (fun n => (differentiable_dualTermC_s ha hR hu₀ hα n).differentiableOn) isOpen_ball
      (fun n s hs => hbound n s hs)
  exact hd.differentiableAt (ball_mem_nhds s₀ one_pos)

/-- The `k`-sum is entire in `s`. -/
theorem differentiable_kSumC_s (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hRk : R < k₀)
    {u₀ : ℝ} (hu₀ : 0 < u₀) (α : ℂ) :
    Differentiable ℂ fun s => ∑' k, kSumTermC a k₀ u₀ s k α := by
  have hRk' : ∀ k : ℕ, R < ((k + k₀ : ℕ) : ℝ) := fun k => by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine differentiable_tsum_of_local_bound (fun k => ?_) fun s₀ => ?_
  · unfold kSumTermC
    exact ((differentiable_const _).mul (kTermEntire a R hR ha u₀ hu₀ _ (hRk' k))).add
      ((differentiable_const _).mul ((kTermEntire a R hR ha u₀ hu₀ _ (hRk' k)).comp
        (differentiable_id.add_const 1)))
  obtain ⟨B₁, hB₁⟩ := kTerm_local_bound ha hR hRk hu₀ s₀
  obtain ⟨B₂, hB₂⟩ := kTerm_local_bound ha hR hRk hu₀ (s₀ + 1)
  have hB₁0 : 0 ≤ B₁ := by
    have := (norm_nonneg _).trans (hB₁ s₀ (mem_ball_self one_pos) k₀ le_rfl); simpa using this
  have hB₂0 : 0 ≤ B₂ := by
    have := (norm_nonneg _).trans (hB₂ (s₀ + 1) (mem_ball_self one_pos) k₀ le_rfl)
    simpa using this
  obtain ⟨hz1, hz2⟩ := norm_geoZ_le (mem_ball_self one_pos : α ∈ ball α 1)
  refine ⟨0, _, summable_kSumBound (2 * π * (|α.im| + 1)) u₀ B₁ B₂ k₀, fun k _ s hs => ?_⟩
  have hs1 : s + 1 ∈ ball (s₀ + 1) 1 := by
    rw [mem_ball, dist_eq_norm] at hs ⊢; simpa using hs
  exact norm_kSumTermC_le hu₀ hB₁0 hB₂0 hz1 hz2 k
    (hB₁ s hs (k + k₀) (Nat.le_add_left _ _)) (hB₂ (s + 1) hs1 (k + k₀) (Nat.le_add_left _ _))

/-- The right-hand side of Theorem 4.1(1) for complex `α`, with `H` and `L_k` given by their
termwise series (entire in `s`). -/
noncomputable def polylogRHSE (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (α s : ℂ) : ℂ :=
  (∑' k, kSumTermC a k₀ u₀ s k α) + ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, dualTermC a u₀ s α n -
    1 / 2 * (∑' n, hSeriesTerm a u₀ n s) -
    ∑ k ∈ Finset.Ico 1 k₀, (geoC (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n s) +
      (k : ℂ) * geoS (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n (s + 1)))

theorem differentiable_polylogRHSE (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hRk : R < k₀)
    {u₀ : ℝ} (hu₀ : 0 < u₀) {α : ℂ} (hα : 0 < margin α) :
    Differentiable ℂ (polylogRHSE a k₀ u₀ α) := by
  have hfin : Differentiable ℂ fun s => ∑ k ∈ Finset.Ico 1 k₀,
      (geoC (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n s) +
        (k : ℂ) * geoS (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n (s + 1))) := by
    refine Differentiable.fun_sum fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.1 hk).1
    exact ((differentiable_const _).mul (differentiable_lSeries ha hR hu₀ hk1)).add
      ((differentiable_const _).mul ((differentiable_lSeries ha hR hu₀ hk1).comp
        (differentiable_id.add_const 1)))
  unfold polylogRHSE
  exact (((differentiable_kSumC_s ha hR hRk hu₀ α).add
    ((differentiable_dualSum_s ha hR hu₀ hα).const_mul _)).sub
      ((differentiable_hSeries ha hR hu₀).const_mul _)).sub hfin

lemma polylogRHSE_eq (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} {u₀ : ℝ} (hu₀ : 0 < u₀)
    (α : ℂ) {s : ℂ} (hs : 1 < s.re) : polylogRHSE a k₀ u₀ α s = polylogRHSC a k₀ u₀ s α := by
  unfold polylogRHSE polylogRHSC lowerH
  rw [(hasSum_hSeries ha hR hu₀ (by linarith)).tsum_eq]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Ico.1 hk).1
  rw [(hasSum_lSeries ha hR hu₀ hk1 hs).tsum_eq,
    (hasSum_lSeries ha hR hu₀ hk1 (s := s + 1) (by simp; linarith)).tsum_eq]

/-- `Li_F^{≥k₀}(s, z)` is entire in `s` for `|z| < 1`. -/
theorem differentiable_lhs_disk (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {α : ℂ} (hα : 0 < α.im) :
    Differentiable ℂ fun s => zetaTail (fun k => F k * geoZ α ^ k) k₀ s := by
  obtain ⟨M, hM⟩ := evalInv_bounded hR ha hRk
  set r := rexp (-(2 * π * α.im))
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff, neg_lt_zero]; positivity
  have h0 : tail k₀ (fun k => F k * geoZ α ^ k) 0 = 0 := by
    simp [tail]; omega
  unfold zetaTail LSeries
  refine differentiable_tsum_of_local_bound (fun n => ?_) fun s₀ => ?_
  · by_cases hn : n = 0
    · subst hn
      have : (fun s => LSeries.term (tail k₀ fun k => F k * geoZ α ^ k) s 0) = fun _ => 0 :=
        funext fun s => by simp [LSeries.term_def]
      rw [this]; exact differentiable_const _
    · have : (fun s => LSeries.term (tail k₀ fun k => F k * geoZ α ^ k) s n) =
          fun s => tail k₀ (fun k => F k * geoZ α ^ k) n * (n : ℂ) ^ (-s) :=
        funext fun s => LSeries.term_def₀ h0 s n
      rw [this]
      exact (differentiable_const _).mul
        (differentiable_neg.const_cpow (Or.inl (Nat.cast_ne_zero.2 hn)))
  set m := ⌈|s₀.re| + 1⌉₊
  refine ⟨k₀, fun n => M * ((n : ℝ) ^ m * r ^ n),
    (summable_pow_mul_geometric_of_norm_lt_one m hr).mul_left M, fun n hn s hs => ?_⟩
  have hn0 : 0 < n := by omega
  rw [LSeries.term_def₀ h0]
  simp only [tail, hn, ite_true]
  have hFn : ‖F n‖ ≤ M := by
    rw [hF n hn]
    have := hM n (by exact_mod_cast hn)
    simpa using this
  have hre : -s.re ≤ m := by
    have h1 := (Complex.abs_re_le_norm (s - s₀)).trans (le_of_lt (by
      rw [mem_ball, dist_eq_norm] at hs; exact hs))
    simp only [Complex.sub_re] at h1
    have := Nat.le_ceil (|s₀.re| + 1)
    have := neg_abs_le s₀.re
    have := abs_le.1 h1
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  rw [norm_mul, norm_mul, norm_pow, norm_geoZ, Complex.norm_natCast_cpow_of_pos hn0]
  simp only [Complex.neg_re]
  calc ‖F n‖ * r ^ n * (n : ℝ) ^ (-s.re) ≤ M * r ^ n * (n : ℝ) ^ (m : ℝ) := by
        have hM0 : 0 ≤ M := (norm_nonneg _).trans hFn
        exact mul_le_mul (mul_le_mul_of_nonneg_right hFn (by positivity))
          (Real.rpow_le_rpow_of_exponent_le hn1 hre) (by positivity) (by positivity)
    _ = M * ((n : ℝ) ^ m * r ^ n) := by rw [Real.rpow_natCast]; ring

/-- **Theorem 4.1(1) inside the disc, for all `s`**: for `z = e^{2πiα}` with
`0 < Im α < min(Re α, 1 - Re α)`, `Li_F^{≥k₀}(s, z)` equals the splitting (with `H`, `L_k` their
termwise series) for every `s ∈ ℂ`. -/
theorem polylogTail_split_disk_all (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {α : ℂ} (hα0 : 0 < α.im) (hα : α ∈ diamond) (s : ℂ) :
    zetaTail (fun k => F k * geoZ α ^ k) k₀ s = polylogRHSE a k₀ u₀ α s := by
  have hm : 0 < margin α := hα
  have hev : (fun s => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) =ᶠ[𝓝 3]
      polylogRHSE a k₀ u₀ α := by
    have hopen : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℝ) < (3 : ℂ).re)] with z hz
    rw [polylogRHSE_eq ha hR hu₀ α (by linarith [show (2 : ℝ) < z.re from hz])]
    exact polylogTail_split_disk ha hR hk₀ hRk hF hz hu₀ hα0 hα
  exact ((differentiable_lhs_disk ha hR hk₀ hRk hF hα0).differentiableOn.analyticOnNhd
    isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    ((differentiable_polylogRHSE ha hR hRk hu₀ hm).differentiableOn.analyticOnNhd isOpen_univ)
    isPreconnected_univ (mem_univ 3) hev (mem_univ s)

end ZetaF
