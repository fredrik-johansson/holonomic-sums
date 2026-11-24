/-
# The main term `M(s)` as a meromorphic function

`M(s) = ∑_n a_n ( √π u₀^{w-1/2} / ((2w-1) Γ(w)) - u₀^w/(2Γ(w+1)) - ∑_{k<k₀} k^{-2w} P(w, k²u₀) )`,
`w = (s+n)/2`, where `k^{-2w} P(w, k²u₀) = k^{-2w} - U_k(w)/Γ(w)` with the entire function `U_k`.
-/
import ZetaF.Continuation.Sums

open MeasureTheory Set Filter Finset
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-- A version of `differentiable_tsum_of_local_bound` at a single point, for terms that are only
differentiable on a ball. -/
theorem differentiableAt_tsum_of_local_bound {T : ℕ → ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hT : ∀ n, DifferentiableOn ℂ (T n) (Metric.ball s₀ r)) {N : ℕ} {b : ℕ → ℝ} (hb : Summable b)
    (hbn : ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ r, ‖T n s‖ ≤ b n) :
    DifferentiableAt ℂ (fun s => ∑' n, T n s) s₀ := by
  have hsub : Metric.closedBall s₀ (r / 2) ⊆ Metric.ball s₀ r :=
    Metric.closedBall_subset_ball (by linarith)
  have hfin : ∀ n, ∃ B, ∀ s ∈ Metric.closedBall s₀ (r / 2), ‖T n s‖ ≤ B := fun n =>
    (isCompact_closedBall s₀ (r / 2)).exists_bound_of_continuousOn ((hT n).continuousOn.mono hsub)
  choose B hB using hfin
  set u : ℕ → ℝ := fun n => if n < N then B n else b n
  have hu : Summable u := by
    have h1 : Summable fun n : ℕ => if n < N then B n - b n else 0 :=
      summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
        simp only [Finset.mem_range] at hn; simp [hn]
    refine (hb.add h1).congr fun n => ?_
    simp only [u]; split_ifs <;> ring
  have hball : Metric.ball s₀ (r / 2) ⊆ Metric.ball s₀ r := Metric.ball_subset_ball (by linarith)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n => (hT n).mono hball) Metric.isOpen_ball (fun n s hs => by
      simp only [u]
      split_ifs with h
      · exact hB n s (Metric.ball_subset_closedBall hs)
      · exact hbn n (by omega) s (hball hs))
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith)))

/-! ### The lower integral `∫₀^{u₀} u^{w-1} e^{-κu} du` -/

/-- `∫₀^{u₀} u^{w-1} e^{-κu} du` (converges for `Re w > 0`). -/
noncomputable def lowerLaplace (κ u₀ : ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioc 0 u₀, (u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)

lemma integrableOn_cpow_mul_exp_Ioi_zero {κ : ℝ} (hκ : 0 < κ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_rpow_mul_exp hw hκ) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    apply ContinuousAt.continuousWithinAt
    exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 hu)).mul (Complex.continuous_ofReal.comp
        (by fun_prop : Continuous fun u : ℝ => rexp (-(κ * u)))).continuousAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    simp

/-- `L(w) + U(w) = Γ(w) κ^{-w}` for `Re w > 0`. -/
lemma lowerLaplace_add_upperLaplace {κ u₀ : ℝ} (hκ : 0 < κ) (hu₀ : 0 < u₀) {w : ℂ}
    (hw : 0 < w.re) :
    lowerLaplace κ u₀ w + upperLaplace κ u₀ w = (1 / (κ : ℂ)) ^ w * Complex.Gamma w := by
  have hint := integrableOn_cpow_mul_exp_Ioi_zero hκ hw
  have e : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) * Complex.exp (-((κ : ℂ) * (t : ℂ))) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w - 1) * (rexp (-(κ * t)) : ℂ) := by
    congr 1; funext t; push_cast; ring_nf
  rw [← Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hκ, e, ← Ioc_union_Ioi_eq_Ioi hu₀.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hu₀.le))]
  rfl

lemma norm_lowerLaplace_le {κ u₀ : ℝ} (hκ : 0 ≤ κ) (hu₀ : 0 < u₀) {w : ℂ} (hw : 0 < w.re) :
    ‖lowerLaplace κ u₀ w‖ ≤ u₀ ^ w.re / w.re := by
  have hint : IntegrableOn (fun u : ℝ => u ^ (w.re - 1)) (Ioc 0 u₀) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine (norm_integral_le_integral_norm _).trans ?_
  calc _ ≤ ∫ u in Ioc 0 u₀, u ^ (w.re - 1) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le]
        simp only [Complex.sub_re, Complex.one_re]
        apply mul_le_of_le_one_right (Real.rpow_nonneg hu.1.le _)
        rw [Real.exp_le_one_iff, neg_nonpos]; exact mul_nonneg hκ hu.1.le
    _ = u₀ ^ w.re / w.re := by
        rw [← intervalIntegral.integral_of_le hu₀.le, integral_rpow (Or.inl (by linarith)),
          Real.zero_rpow (by linarith)]
        simp

/-- `k^{-2w} - U_k(w)/Γ(w) = L_k(w)/Γ(w)` for `Re w > 0` (this is `k^{-2w} P(w, k²u₀)`). -/
lemma cpow_sub_upperLaplace {k u₀ : ℝ} (hk : 0 < k) (hu₀ : 0 < u₀) {w : ℂ} (hw : 0 < w.re) :
    (k : ℂ) ^ (-2 * w) - (Complex.Gamma w)⁻¹ * upperLaplace (k ^ 2) u₀ w =
      (Complex.Gamma w)⁻¹ * lowerLaplace (k ^ 2) u₀ w := by
  have h := lowerLaplace_add_upperLaplace (κ := k ^ 2) (by positivity) hu₀ hw
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  push_cast at h
  rw [show (1 / ((k : ℂ) ^ 2)) = ((1 / k ^ 2 : ℝ) : ℂ) by push_cast; ring] at h
  rw [show ((1 / k ^ 2 : ℝ) : ℂ) = 1 / ((k ^ 2 : ℝ) : ℂ) by push_cast; ring, one_div_sq_cpow hk] at h
  have e : (k : ℂ) ^ (-2 * w) = (lowerLaplace (k ^ 2) u₀ w + upperLaplace (k ^ 2) u₀ w) *
      (Complex.Gamma w)⁻¹ := by rw [h]; field_simp
  rw [e]; ring

/-! ### The series for `M(s)` -/

/-- A term of the series for the main term. -/
noncomputable def mainSeriesTerm (a : ℕ → ℂ) (u₀ : ℝ) (k₀ : ℕ) (n : ℕ) (s : ℂ) : ℂ :=
  a n * ((√π : ℂ) * (u₀ : ℂ) ^ ((s + n) / 2 - 1 / 2) * (Complex.Gamma ((s + n) / 2))⁻¹ /
      (s + n - 1) -
    (u₀ : ℂ) ^ ((s + n) / 2) * (Complex.Gamma ((s + n) / 2 + 1))⁻¹ / 2 -
    ∑ k ∈ Ico 1 k₀, ((k : ℂ) ^ (-2 * ((s + n) / 2)) -
      (Complex.Gamma ((s + n) / 2))⁻¹ * upperLaplace ((k : ℝ) ^ 2) u₀ ((s + n) / 2)))

lemma differentiableAt_mainSeriesTerm {u₀ : ℝ} (hu₀ : 0 < u₀) (k₀ n : ℕ) {s : ℂ}
    (hs : s + n - 1 ≠ 0) : DifferentiableAt ℂ (mainSeriesTerm a u₀ k₀ n) s := by
  have hw : DifferentiableAt ℂ (fun s : ℂ => (s + n) / 2) s := (differentiable_half_shift n) s
  have hΓ : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma ((s + n) / 2))⁻¹) s :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp s hw
  have hΓ1 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma ((s + n) / 2 + 1))⁻¹) s :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp s (hw.add_const 1)
  have hu : (u₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu₀.ne'
  unfold mainSeriesTerm
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · apply DifferentiableAt.sub
    · exact ((((differentiableAt_const _).mul ((hw.sub_const _).const_cpow (Or.inl hu))).mul
        hΓ).div ((differentiableAt_id.add_const _).sub_const _) hs)
    · exact ((hw.const_cpow (Or.inl hu)).mul hΓ1).div_const _
  · apply DifferentiableAt.fun_sum
    intro k hk
    have hk0 : (k : ℂ) ≠ 0 := by
      simp only [Finset.mem_Ico] at hk; exact_mod_cast (by omega : k ≠ 0)
    have hk' : 0 < (k : ℝ) ^ 2 := by
      simp only [Finset.mem_Ico] at hk
      have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      positivity
    exact ((hw.const_mul (-2)).const_cpow (Or.inl hk0)).sub
      (hΓ.mul ((differentiable_upperLaplace hk' hu₀).differentiableAt.comp s hw))

/-- Locally uniform bound for the main-term series (terms with `Re w ≥ 1`). -/
lemma mainSeries_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (k₀ : ℕ) (s₀ : ℂ) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧ ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1,
      ‖mainSeriesTerm a u₀ k₀ n s‖ ≤ b n := by
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
  set K : ℝ := √π * u₀ ^ (-(1 / 2 : ℝ)) + 1 / 2 + k₀
  have hK : 0 ≤ K := by positivity
  refine ⟨N, fun n => Ca * C * K * rexp (u₀ / l) * l ^ ((s₀.re - 1) / 2) * (R * √l) ^ n, ?_,
    fun n hn s hs => ?_⟩
  · exact (summable_geometric_of_lt_one (mul_nonneg hR (Real.sqrt_nonneg _)) hq).mul_left _
  obtain ⟨h1, h2, h3⟩ := hN n hn s hs
  obtain ⟨h1', -, h3'⟩ := hN (n + 2) (by omega) s hs
  set w := (s + n) / 2 with hw
  set x := w.re
  have ew : (s + ((n + 2 : ℕ) : ℂ)) / 2 = w + 1 := by rw [hw]; push_cast; ring
  rw [ew] at h3'
  have hx : 1 ≤ x := h1
  have hx0 : 0 < x := by linarith
  have hG := Real.Gamma_pos_of_pos hx0
  have hG1 := Real.Gamma_pos_of_pos (show 0 < x + 1 by linarith)
  have hΓ : ‖(Complex.Gamma w)⁻¹‖ ≤ C / Real.Gamma x := by rw [le_div_iff₀ hG]; exact h3
  have hΓ1 : ‖(Complex.Gamma (w + 1))⁻¹‖ ≤ C / Real.Gamma (x + 1) := by
    rw [le_div_iff₀ hG1]; simpa using h3'
  have hxΓ : x * Real.Gamma x = Real.Gamma (x + 1) := (Real.Gamma_add_one hx0.ne').symm
  -- the three pieces
  have hA : ‖(√π : ℂ) * (u₀ : ℂ) ^ (w - 1 / 2) * (Complex.Gamma w)⁻¹ / (s + n - 1)‖ ≤
      √π * u₀ ^ (-(1 / 2 : ℝ)) * C * (u₀ ^ x / Real.Gamma (x + 1)) := by
    have hden : x ≤ ‖s + n - 1‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      have : (s + n - 1).re = 2 * x - 1 := by simp [x, hw]; ring
      rw [this]; linarith
    rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu₀,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
    rw [div_le_iff₀ (lt_of_lt_of_le hx0 hden)]
    have e : u₀ ^ (x - 1 / 2) = u₀ ^ (-(1 / 2 : ℝ)) * u₀ ^ x := by
      rw [← Real.rpow_add hu₀]; ring_nf
    rw [e]
    calc √π * (u₀ ^ (-(1 / 2 : ℝ)) * u₀ ^ x) * ‖(Complex.Gamma w)⁻¹‖
        ≤ √π * (u₀ ^ (-(1 / 2 : ℝ)) * u₀ ^ x) * (C / Real.Gamma x) :=
          mul_le_mul_of_nonneg_left hΓ (by positivity)
      _ = √π * u₀ ^ (-(1 / 2 : ℝ)) * C * (u₀ ^ x / Real.Gamma (x + 1)) * x := by
          rw [← hxΓ]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  have hB : ‖(u₀ : ℂ) ^ w * (Complex.Gamma (w + 1))⁻¹ / 2‖ ≤
      1 / 2 * C * (u₀ ^ x / Real.Gamma (x + 1)) := by
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu₀]
    simp only [Complex.norm_ofNat]
    calc u₀ ^ x * ‖(Complex.Gamma (w + 1))⁻¹‖ / 2 ≤ u₀ ^ x * (C / Real.Gamma (x + 1)) / 2 := by
          gcongr
      _ = _ := by ring
  have hCk : ∀ k ∈ Finset.Ico 1 k₀, ‖(k : ℂ) ^ (-2 * w) - (Complex.Gamma w)⁻¹ *
      upperLaplace ((k : ℝ) ^ 2) u₀ w‖ ≤ C * (u₀ ^ x / Real.Gamma (x + 1)) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by
      simp only [Finset.mem_Ico] at hk; exact_mod_cast (by omega : 0 < k)
    have hid := cpow_sub_upperLaplace (k := (k : ℝ)) hk0 hu₀ hx0
    simp only [Complex.ofReal_natCast] at hid
    rw [hid, norm_mul]
    calc ‖(Complex.Gamma w)⁻¹‖ * ‖lowerLaplace ((k : ℝ) ^ 2) u₀ w‖
        ≤ (C / Real.Gamma x) * (u₀ ^ x / x) :=
          mul_le_mul hΓ (norm_lowerLaplace_le (by positivity) hu₀ hx0) (norm_nonneg _)
            (by positivity)
      _ = C * (u₀ ^ x / Real.Gamma (x + 1)) := by rw [← hxΓ]; field_simp
  have hsumk : ‖∑ k ∈ Ico 1 k₀, ((k : ℂ) ^ (-2 * w) - (Complex.Gamma w)⁻¹ *
      upperLaplace ((k : ℝ) ^ 2) u₀ w)‖ ≤ k₀ * (C * (u₀ ^ x / Real.Gamma (x + 1))) := by
    refine (norm_sum_le _ _).trans ((sum_le_sum hCk).trans ?_)
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le k₀ 1
  have hE := rpow_div_Gamma_le hx0 hu₀.le hl0
  have hpow : l ^ x ≤ l ^ ((s₀.re - 1) / 2) * (√l) ^ n := by
    rw [← rpow_half_add_nat hl0]
    exact Real.rpow_le_rpow_of_exponent_ge hl0 hl1 (by linarith)
  have hQ : u₀ ^ x / Real.Gamma (x + 1) ≤ rexp (u₀ / l) * (l ^ ((s₀.re - 1) / 2) * (√l) ^ n) :=
    hE.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  unfold mainSeriesTerm
  rw [← hw, norm_mul]
  calc ‖a n‖ * ‖_‖ ≤ (Ca * R ^ n) * (C * K * (u₀ ^ x / Real.Gamma (x + 1))) := by
        apply mul_le_mul (hCa n) _ (norm_nonneg _) (by positivity)
        refine (norm_sub_le _ _).trans ?_
        refine (add_le_add ((norm_sub_le _ _).trans (add_le_add hA hB)) hsumk).trans (le_of_eq ?_)
        simp only [K]; ring
    _ ≤ (Ca * R ^ n) * (C * K * (rexp (u₀ / l) * (l ^ ((s₀.re - 1) / 2) * (√l) ^ n))) := by
        gcongr
    _ = _ := by simp only [mul_pow]; ring

/-- The series for `M(s)` is holomorphic away from the points `s = 1 - n`. -/
theorem differentiableOn_mainSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (k₀ : ℕ) :
    DifferentiableOn ℂ (fun s => ∑' n, mainSeriesTerm a u₀ k₀ n s)
      {s | ∀ n : ℕ, s ≠ 1 - n} := by
  intro s₀ hs₀
  obtain ⟨N₀, b, hb, hbn₀⟩ := mainSeries_local_bound ha hR hu₀ k₀ s₀
  obtain ⟨N₁, C, -, hN₁⟩ := local_gamma_control s₀
  set N := max N₀ N₁
  have hbn : ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1, ‖mainSeriesTerm a u₀ k₀ n s‖ ≤ b n :=
    fun n hn => hbn₀ n (le_of_max_le_left hn)
  have hV : IsOpen {s : ℂ | ∀ n ∈ Finset.range N, s + n - 1 ≠ 0} := by
    simp only [setOf_forall]
    exact isOpen_biInter_finset fun n _ => isOpen_ne_fun (by fun_prop) continuous_const
  have hs₀V : s₀ ∈ {s : ℂ | ∀ n ∈ Finset.range N, s + n - 1 ≠ 0} := fun n _ h =>
    hs₀ n (by linear_combination h)
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV s₀ hs₀V
  set r := min ε 1
  have hr : 0 < r := lt_min hε one_pos
  have hball : Metric.ball s₀ r ⊆ Metric.ball s₀ 1 := Metric.ball_subset_ball (min_le_right _ _)
  refine (differentiableAt_tsum_of_local_bound hr (fun n s hs => ?_) hb
    fun n hn s hs => hbn n hn s (hball hs)).differentiableWithinAt
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_mainSeriesTerm hu₀
  by_cases hn : n < N
  · exact hεV (Metric.ball_subset_ball (min_le_left _ _) hs) n (Finset.mem_range.2 hn)
  · obtain ⟨h1, -, -⟩ := hN₁ n (le_of_max_le_right (not_lt.1 hn)) s (hball hs)
    intro h
    have : (s + n - 1).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at this
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re] at h1
    linarith

end ZetaF
