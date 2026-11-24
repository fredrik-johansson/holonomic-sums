/-
# The dual integrals on the slit plane

For `Re c > 0` the dual integral `D(c, w) = ∫₀^{u₀} u^{w-1} u^{-1/2} e^{-c/u} du` (`lowerDualC`)
becomes, after `u = 1/v`, the integral `∫_{x₀}^∞ v^{-w-1/2} e^{-cv} dv` with `x₀ = 1/u₀`.  We
continue it to the slit plane `ℂ ∖ (-∞, 0]` by turning the ray of integration: for `Re p > 0`,
`Re(cp) > 0`,
`Φ(c, p) = p ∫₀^∞ (x₀ + tp)^b e^{-c(x₀+tp)} dt` (`rayInt`, `b = -w - 1/2`).
`Φ` is holomorphic in `c` and in `p` (`differentiableAt_rayInt_c`, `differentiableAt_rayInt_p`), and
invariant under `p ↦ λp` for real `λ > 0` (substitution `t ↦ λt`), so `∂_p Φ · p = 0`: `Φ(c, ·)` is
constant on the convex set `{Re p > 0, Re(cp) > 0}` (`rayInt_eq_of_mem`).  This is the contour
rotation, without Cauchy's theorem for sectors.

The direction `p(c) = 1 - i Im c/(|c| + Re c)` has `Re(c p(c)) = |c| > 0` on the slit plane, so
`Dslit c u₀ w = Φ(c, p(c))` is defined on the whole slit plane; it is holomorphic there
(`differentiableOn_Dslit`) and equals `lowerDualC c u₀ w` for `Re c > 0` (`Dslit_eq_lowerDualC`).

Termwise, `J^{(0)}_s(c) = ∑ a_n/Γ((s+n)/2) D(c, (s+n)/2)` and its odd analogue continue to the slit
plane (`JslitE`, `JslitO`), holomorphic in `c` (`differentiableOn_JslitE`, `differentiableOn_JslitO`)
and equal to `geoJC` for `Re c > 0` (`JslitE_eq`, `JslitO_eq`).

Rays into the lower half-plane (`Im p < 0`) stay in the slit plane as well; the direction
`p = -1 - i` is admissible on `Im c > Re c`, which contains the negative real axis.  This gives the
boundary values `Dup`, `JupE`, `JupO` from `Im c > 0` on the cut (`tendsto_JslitE_JupE`).
-/
import ZetaF.Polylog.DiskEntire
import Mathlib.Analysis.Complex.Liouville

open MeasureTheory Set Filter Metric Asymptotics
open scoped Real Topology

namespace ZetaF

/-! ### Holomorphic parametric integrals -/

/-- A parametric integral of functions holomorphic in the parameter, dominated by a fixed
integrable function, is holomorphic (Cauchy's estimate bounds the derivatives). -/
theorem differentiableAt_integral_of_dominated {β : Type*} [MeasurableSpace β] {μ : Measure β}
    {F : ℂ → β → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) {g : β → ℝ} (hg : Integrable g μ)
    (hmeas : ∀ z ∈ ball z₀ r, AEStronglyMeasurable (F z) μ)
    (hdiff : ∀ᵐ x ∂μ, DifferentiableOn ℂ (F · x) (ball z₀ r))
    (hbound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ r, ‖F z x‖ ≤ g x) :
    DifferentiableAt ℂ (fun z => ∫ x, F z x ∂μ) z₀ := by
  have hr2 : 0 < r / 2 := by linarith
  have hsub : ∀ z ∈ ball z₀ (r / 2), closedBall z (r / 2) ⊆ ball z₀ r := fun z hz w hw => by
    rw [mem_closedBall] at hw; rw [mem_ball] at hz ⊢
    linarith [dist_triangle w z z₀]
  have hsub' : ball z₀ (r / 2) ⊆ ball z₀ r := ball_subset_ball (by linarith)
  have hF_int : Integrable (F z₀) μ :=
    Integrable.mono' hg (hmeas z₀ (mem_ball_self hr))
      (hbound.mono fun x hx => hx z₀ (mem_ball_self hr))
  -- measurability of the derivative, as a limit of difference quotients
  set h : ℕ → ℂ := fun n => ((r / 2 / (n + 2) : ℝ) : ℂ)
  have hpos : ∀ n : ℕ, 0 < r / 2 / (n + 2) := fun n => by positivity
  have hh0 : ∀ n, h n ≠ 0 := fun n => Complex.ofReal_ne_zero.2 (hpos n).ne'
  have hhball : ∀ n, z₀ + h n ∈ ball z₀ r := fun n => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (hpos n).le]
    calc r / 2 / (n + 2) ≤ r / 2 / 1 :=
          div_le_div_of_nonneg_left hr2.le one_pos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      _ < r := by linarith
  have htend : Tendsto h atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n => hh0 n)
    have : Tendsto (fun n : ℕ => r / 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact h1.const_div_atTop _
    have := (Complex.continuous_ofReal.tendsto 0).comp this
    rw [Complex.ofReal_zero] at this
    exact this
  have hF'_meas : AEStronglyMeasurable (fun x => deriv (F · x) z₀) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n x => (h n)⁻¹ • (F (z₀ + h n) x - F z₀ x)) (fun n => ?_) ?_
    · exact ((hmeas _ (hhball n)).sub (hmeas z₀ (mem_ball_self hr))).const_smul (h n)⁻¹
    · refine hdiff.mono fun x hx => ?_
      have hd : HasDerivAt (F · x) (deriv (F · x) z₀) z₀ :=
        (hx.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
      exact hd.tendsto_slope_zero.comp htend
  have hderiv_bound : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ (r / 2), ‖deriv (F · x) z‖ ≤ g x / (r / 2) := by
    filter_upwards [hdiff, hbound] with x hx hxb z hz
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2
      (hx.diffContOnCl_ball (hsub z hz)) fun w hw => hxb w (hsub z hz (sphere_subset_closedBall hw))
  have hdiff' : ∀ᵐ x ∂μ, ∀ z ∈ ball z₀ (r / 2), HasDerivAt (F · x) (deriv (F · x) z) z := by
    filter_upwards [hdiff] with x hx z hz
    exact (hx.differentiableAt (isOpen_ball.mem_nhds (hsub' hz))).hasDerivAt
  have hmeas' : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) μ :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) hmeas
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds z₀ hr2) hmeas' hF_int
    hF'_meas hderiv_bound (hg.div_const _) hdiff').2.differentiableAt

/-! ### The ray integral -/

/-- The integrand `(x₀ + tp)^b e^{-c(x₀+tp)}`. -/
noncomputable def rayF (x₀ : ℝ) (b c p : ℂ) (t : ℝ) : ℂ :=
  ((x₀ : ℂ) + t * p) ^ b * Complex.exp (-(c * ((x₀ : ℂ) + t * p)))

/-- `Φ(c, p) = p ∫₀^∞ (x₀ + tp)^b e^{-c(x₀+tp)} dt`: the integral of `v^b e^{-cv}` along the ray
from `x₀` in the direction `p`. -/
noncomputable def rayInt (x₀ : ℝ) (b c p : ℂ) : ℂ := p * ∫ t in Ioi (0 : ℝ), rayF x₀ b c p t

section Ray

variable {x₀ : ℝ} {b c p : ℂ} {t : ℝ}

lemma ray_re (x₀ : ℝ) (p : ℂ) (t : ℝ) : ((x₀ : ℂ) + t * p).re = x₀ + t * p.re := by simp

lemma ray_re_ge (hp : 0 ≤ p.re) (ht : 0 ≤ t) : x₀ ≤ ((x₀ : ℂ) + t * p).re := by
  rw [ray_re]; nlinarith

lemma ray_mem_slitPlane (hx₀ : 0 < x₀) (hp : 0 ≤ p.re) (ht : 0 ≤ t) :
    (x₀ : ℂ) + t * p ∈ Complex.slitPlane :=
  Or.inl (lt_of_lt_of_le hx₀ (ray_re_ge hp ht))

lemma ray_norm_ge (hp : 0 ≤ p.re) (ht : 0 ≤ t) : x₀ ≤ ‖(x₀ : ℂ) + t * p‖ :=
  (ray_re_ge hp ht).trans (Complex.re_le_norm _)

lemma ray_norm_le (hx₀ : 0 ≤ x₀) {q : ℝ} (hq : ‖p‖ ≤ q) (ht : 0 ≤ t) :
    ‖(x₀ : ℂ) + t * p‖ ≤ x₀ + t * q := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hx₀,
    Real.norm_of_nonneg ht]
  nlinarith

lemma rpow_le_add_of_mem {y A B β : ℝ} (hA : 0 < A) (h1 : A ≤ y) (h2 : y ≤ B) :
    y ^ β ≤ A ^ β + B ^ β := by
  rcases le_total 0 β with hβ | hβ
  · exact (Real.rpow_le_rpow (hA.le.trans h1) h2 hβ).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hA.le _))
  · exact (Real.rpow_le_rpow_of_nonpos hA h1 hβ).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hA.le.trans (h1.trans h2)) _))

lemma norm_cpow_le_of_re_pos {v : ℂ} (hv : 0 < v.re) (b : ℂ) :
    ‖v ^ b‖ ≤ ‖v‖ ^ b.re * rexp (π * |b.im|) := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  rw [Complex.norm_cpow_of_ne_zero hv0, div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  have := Complex.abs_arg_le_pi v
  calc -(Complex.arg v * b.im) ≤ |Complex.arg v * b.im| := neg_le_abs _
    _ = |Complex.arg v| * |b.im| := abs_mul _ _
    _ ≤ π * |b.im| := mul_le_mul_of_nonneg_right this (abs_nonneg _)

lemma re_mul_ray (x₀ : ℝ) (c p : ℂ) (t : ℝ) :
    (c * ((x₀ : ℂ) + t * p)).re = x₀ * c.re + t * (c * p).re := by
  have : c * ((x₀ : ℂ) + t * p) = (x₀ : ℂ) * c + (t : ℂ) * (c * p) := by ring
  rw [this, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- Pointwise bound for the ray integrand. -/
lemma norm_rayF_le (hx₀ : 0 < x₀) (hp : 0 < p.re) {q : ℝ} (hq : ‖p‖ ≤ q) (ht : 0 ≤ t) :
    ‖rayF x₀ b c p t‖ ≤ rexp (π * |b.im|) * (x₀ ^ b.re + (x₀ + t * q) ^ b.re) *
      (rexp (-(x₀ * c.re)) * rexp (-((c * p).re * t))) := by
  have hv : 0 < ((x₀ : ℂ) + t * p).re := lt_of_lt_of_le hx₀ (ray_re_ge hp.le ht)
  unfold rayF
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, re_mul_ray, ← Real.exp_add]
  have h1 := norm_cpow_le_of_re_pos hv b
  have h2 := rpow_le_add_of_mem (β := b.re) hx₀ (ray_norm_ge hp.le ht) (ray_norm_le hx₀.le hq ht)
  have e : -(x₀ * c.re + t * (c * p).re) = -(x₀ * c.re) + -((c * p).re * t) := by ring
  rw [e]
  have hE := (Real.exp_pos (-(x₀ * c.re) + -((c * p).re * t))).le
  calc ‖((x₀ : ℂ) + t * p) ^ b‖ * rexp (-(x₀ * c.re) + -((c * p).re * t))
      ≤ (‖(x₀ : ℂ) + t * p‖ ^ b.re * rexp (π * |b.im|)) *
          rexp (-(x₀ * c.re) + -((c * p).re * t)) := mul_le_mul_of_nonneg_right h1 hE
    _ ≤ ((x₀ ^ b.re + (x₀ + t * q) ^ b.re) * rexp (π * |b.im|)) *
          rexp (-(x₀ * c.re) + -((c * p).re * t)) := by gcongr
    _ = _ := by ring

/-- The dominating function `(x₀^β + (x₀ + tq)^β) e^{-κt}`. -/
noncomputable def domF (x₀ β q κ : ℝ) (t : ℝ) : ℝ := (x₀ ^ β + (x₀ + t * q) ^ β) * rexp (-(κ * t))

lemma domF_nonneg (hx₀ : 0 < x₀) {β q κ : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) : 0 ≤ domF x₀ β q κ t := by
  unfold domF
  have : 0 ≤ x₀ + t * q := by nlinarith
  positivity

lemma integrableOn_domF (hx₀ : 0 < x₀) (β : ℝ) {q κ : ℝ} (hq : 0 < q) (hκ : 0 < κ) :
    IntegrableOn (domF x₀ β q κ) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => x₀ ^ β * rexp (-(κ * t))) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 hκ).const_mul (x₀ ^ β)
    have e : (fun t : ℝ => x₀ ^ β * rexp (-(κ * t))) = fun t => x₀ ^ β * rexp (-κ * t) := by
      funext t; ring_nf
    rw [e]; exact this
  have h2 : IntegrableOn (fun t : ℝ => (x₀ + t * q) ^ β * rexp (-(κ * t))) (Ioi 0) := by
    refine integrable_of_isBigO_exp_neg (b := κ / 2) (by positivity) ?_ ?_
    · intro t ht
      have : 0 < x₀ + t * q := by have : (0 : ℝ) ≤ t := ht; nlinarith
      refine ContinuousAt.continuousWithinAt ?_
      exact (ContinuousAt.rpow_const (f := fun t : ℝ => x₀ + t * q) (by fun_prop)
        (Or.inl this.ne')).mul (by fun_prop)
    · set b' := κ / (2 * q)
      have hb' : 0 < b' := by positivity
      have htend : Tendsto (fun t : ℝ => x₀ + t * q) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hq)
      have h1 : (fun t : ℝ => (x₀ + t * q) ^ β) =O[atTop] fun t => rexp (b' * (x₀ + t * q)) :=
        ((isLittleO_rpow_exp_pos_mul_atTop β hb').comp_tendsto htend).isBigO
      have h2 := h1.mul (isBigO_refl (fun t : ℝ => rexp (-(κ * t))) atTop)
      refine h2.trans ?_
      have e : ∀ t : ℝ, rexp (b' * (x₀ + t * q)) * rexp (-(κ * t)) =
          rexp (b' * x₀) * rexp (-(κ / 2) * t) := by
        intro t; rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [b']; field_simp; ring
      simp_rw [e]
      exact (isBigO_refl _ _).const_mul_left _
  exact (h1.add h2).congr_fun (fun t _ => by simp only [domF, Pi.add_apply]; ring) measurableSet_Ioi

lemma continuousOn_rayF (hx₀ : 0 < x₀) (hp : 0 ≤ p.re) :
    ContinuousOn (rayF x₀ b c p) (Ici 0) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  have hv : ContinuousAt (fun t : ℝ => (x₀ : ℂ) + t * p) t := by fun_prop
  exact (hv.cpow continuousAt_const (ray_mem_slitPlane hx₀ hp ht)).mul (by fun_prop)

lemma aestronglyMeasurable_rayF (hx₀ : 0 < x₀) (hp : 0 ≤ p.re) :
    AEStronglyMeasurable (rayF x₀ b c p) (volume.restrict (Ioi 0)) :=
  ((continuousOn_rayF hx₀ hp).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi

/-- The radius of a common neighbourhood of `(c₀, p₀)`. -/
noncomputable def rayRad (c₀ p₀ : ℂ) : ℝ := min (min 1 (p₀.re / 2)) ((c₀ * p₀).re / (2 * (‖c₀‖ + ‖p₀‖ + 1)))

lemma rayRad_pos {c₀ p₀ : ℂ} (hp₀ : 0 < p₀.re) (hc₀ : 0 < (c₀ * p₀).re) : 0 < rayRad c₀ p₀ := by
  unfold rayRad; positivity

lemma rayRad_props {c₀ p₀ c p : ℂ} (_hp₀ : 0 < p₀.re) (_hc₀ : 0 < (c₀ * p₀).re)
    (hc : ‖c - c₀‖ < rayRad c₀ p₀) (hp : ‖p - p₀‖ < rayRad c₀ p₀) :
    p₀.re / 2 ≤ p.re ∧ (c₀ * p₀).re / 2 ≤ (c * p).re ∧ ‖p‖ ≤ ‖p₀‖ + 1 ∧ ‖c‖ ≤ ‖c₀‖ + 1 := by
  set r := rayRad c₀ p₀
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ p₀.re / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ (c₀ * p₀).re / (2 * (‖c₀‖ + ‖p₀‖ + 1)) := min_le_right _ _
  have hpn : ‖p‖ ≤ ‖p₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' p p₀; linarith
  have hcn : ‖c‖ ≤ ‖c₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c c₀; linarith
  refine ⟨?_, ?_, hpn, hcn⟩
  · have := Complex.abs_re_le_norm (p - p₀)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le (p.re - p₀.re)]
  · have e : c * p - c₀ * p₀ = (c - c₀) * p + c₀ * (p - p₀) := by ring
    have hn : ‖c * p - c₀ * p₀‖ ≤ r * (‖c₀‖ + ‖p₀‖ + 1) := by
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖c - c₀‖ * ‖p‖ ≤ r * (‖p₀‖ + 1) :=
        mul_le_mul hc.le hpn (norm_nonneg _) (le_trans (norm_nonneg _) hc.le)
      have h2 : ‖c₀‖ * ‖p - p₀‖ ≤ ‖c₀‖ * r := mul_le_mul_of_nonneg_left hp.le (norm_nonneg _)
      linarith
    have hr3' : r * (‖c₀‖ + ‖p₀‖ + 1) ≤ (c₀ * p₀).re / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (‖c₀‖ + ‖p₀‖ + 1))] at hr3
      linarith
    have := Complex.abs_re_le_norm (c * p - c₀ * p₀)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le ((c * p).re - (c₀ * p₀).re)]

/-- Uniform domination of the integrand near `(c₀, p₀)`. -/
lemma norm_rayF_le_dom (hx₀ : 0 < x₀) {c₀ p₀ : ℂ} (hp₀ : 0 < p₀.re) (hc₀ : 0 < (c₀ * p₀).re)
    (hc : ‖c - c₀‖ < rayRad c₀ p₀) (hp : ‖p - p₀‖ < rayRad c₀ p₀) (ht : 0 ≤ t) :
    ‖rayF x₀ b c p t‖ ≤ (rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))) *
      domF x₀ b.re (‖p₀‖ + 1) ((c₀ * p₀).re / 2) t := by
  obtain ⟨h1, h2, h3, h4⟩ := rayRad_props hp₀ hc₀ hc hp
  have hpre : 0 < p.re := by linarith
  refine (norm_rayF_le hx₀ hpre h3 ht).trans ?_
  have hA : rexp (-(x₀ * c.re)) ≤ rexp (x₀ * (‖c₀‖ + 1)) := by
    rw [Real.exp_le_exp]
    have := neg_abs_le c.re
    have := Complex.abs_re_le_norm c
    nlinarith
  have hB : rexp (-((c * p).re * t)) ≤ rexp (-((c₀ * p₀).re / 2 * t)) := by
    rw [Real.exp_le_exp]; nlinarith
  have hS : 0 ≤ x₀ ^ b.re + (x₀ + t * (‖p₀‖ + 1)) ^ b.re := by
    have : 0 ≤ x₀ + t * (‖p₀‖ + 1) := by positivity
    positivity
  unfold domF
  calc rexp (π * |b.im|) * (x₀ ^ b.re + (x₀ + t * (‖p₀‖ + 1)) ^ b.re) *
        (rexp (-(x₀ * c.re)) * rexp (-((c * p).re * t)))
      ≤ rexp (π * |b.im|) * (x₀ ^ b.re + (x₀ + t * (‖p₀‖ + 1)) ^ b.re) *
        (rexp (x₀ * (‖c₀‖ + 1)) * rexp (-((c₀ * p₀).re / 2 * t))) := by gcongr
    _ = _ := by ring

lemma integrableOn_rayF (hx₀ : 0 < x₀) (hp : 0 < p.re) (hc : 0 < (c * p).re) :
    IntegrableOn (rayF x₀ b c p) (Ioi 0) := by
  have hr := rayRad_pos hp hc
  have hc0 : ‖c - c‖ < rayRad c p := by rw [sub_self, norm_zero]; exact hr
  have hp0 : ‖p - p‖ < rayRad c p := by rw [sub_self, norm_zero]; exact hr
  have hdom : IntegrableOn (fun t => (rexp (π * |b.im|) * rexp (x₀ * (‖c‖ + 1))) *
      domF x₀ b.re (‖p‖ + 1) ((c * p).re / 2) t) (Ioi 0) :=
    (integrableOn_domF hx₀ b.re (by positivity) (by positivity)).const_mul _
  refine Integrable.mono' hdom (aestronglyMeasurable_rayF hx₀ hp.le) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  exact norm_rayF_le_dom hx₀ hp hc hc0 hp0 (le_of_lt ht)

/-- `Φ(·, p₀)` is holomorphic on `Re(c p₀) > 0`. -/
theorem differentiableAt_rayInt_c (hx₀ : 0 < x₀) {c₀ p₀ : ℂ} (hp₀ : 0 < p₀.re)
    (hc₀ : 0 < (c₀ * p₀).re) : DifferentiableAt ℂ (fun c => rayInt x₀ b c p₀) c₀ := by
  have hr := rayRad_pos hp₀ hc₀
  have hp0 : ‖p₀ - p₀‖ < rayRad c₀ p₀ := by rw [sub_self, norm_zero]; exact hr
  have hdom : IntegrableOn (fun t => (rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))) *
      domF x₀ b.re (‖p₀‖ + 1) ((c₀ * p₀).re / 2) t) (Ioi 0) :=
    (integrableOn_domF hx₀ b.re (by positivity) (by positivity)).const_mul _
  show DifferentiableAt ℂ (fun c => p₀ * ∫ t in Ioi (0 : ℝ), rayF x₀ b c p₀ t) c₀
  refine (differentiableAt_const p₀).mul ?_
  refine differentiableAt_integral_of_dominated (F := fun c t => rayF x₀ b c p₀ t) hr hdom
    (fun c _ => aestronglyMeasurable_rayF hx₀ hp₀.le) (Eventually.of_forall fun t => ?_) ?_
  · intro c _
    unfold rayF
    exact ((differentiableAt_const _).mul ((differentiableAt_id.mul
      (differentiableAt_const _)).neg.cexp)).differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht c hc => ?_)
    rw [mem_ball, dist_eq_norm] at hc
    exact norm_rayF_le_dom hx₀ hp₀ hc₀ hc hp0 (le_of_lt ht)

/-- `Φ(c₀, ·)` is holomorphic on `{Re p > 0, Re(c₀ p) > 0}`. -/
theorem differentiableAt_rayInt_p (hx₀ : 0 < x₀) {c₀ p₀ : ℂ} (hp₀ : 0 < p₀.re)
    (hc₀ : 0 < (c₀ * p₀).re) : DifferentiableAt ℂ (fun p => rayInt x₀ b c₀ p) p₀ := by
  have hr := rayRad_pos hp₀ hc₀
  have hc0 : ‖c₀ - c₀‖ < rayRad c₀ p₀ := by rw [sub_self, norm_zero]; exact hr
  have hdom : IntegrableOn (fun t => (rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))) *
      domF x₀ b.re (‖p₀‖ + 1) ((c₀ * p₀).re / 2) t) (Ioi 0) :=
    (integrableOn_domF hx₀ b.re (by positivity) (by positivity)).const_mul _
  show DifferentiableAt ℂ (fun p => p * ∫ t in Ioi (0 : ℝ), rayF x₀ b c₀ p t) p₀
  refine differentiableAt_id.mul ?_
  refine differentiableAt_integral_of_dominated (F := fun p t => rayF x₀ b c₀ p t) hr hdom
    (fun p hp => ?_) ?_ ?_
  · rw [mem_ball, dist_eq_norm] at hp
    exact aestronglyMeasurable_rayF hx₀ (by linarith [(rayRad_props hp₀ hc₀ hc0 hp).1])
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht p hp => ?_)
    rw [mem_ball, dist_eq_norm] at hp
    have hpre : 0 < p.re := by linarith [(rayRad_props hp₀ hc₀ hc0 hp).1]
    have hv : DifferentiableAt ℂ (fun p : ℂ => (x₀ : ℂ) + t * p) p := by fun_prop
    unfold rayF
    exact ((hv.cpow_const (ray_mem_slitPlane hx₀ hpre.le (le_of_lt ht))).mul
      ((differentiableAt_const c₀).mul hv).neg.cexp).differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht p hp => ?_)
    rw [mem_ball, dist_eq_norm] at hp
    exact norm_rayF_le_dom hx₀ hp₀ hc₀ hc0 hp (le_of_lt ht)

/-- Invariance under `p ↦ λp`, `λ > 0` (substitution `t ↦ λt`). -/
lemma rayInt_ofReal_mul (x₀ : ℝ) (b c p : ℂ) {l : ℝ} (hl : 0 < l) :
    rayInt x₀ b c ((l : ℂ) * p) = rayInt x₀ b c p := by
  unfold rayInt
  have h := integral_comp_mul_left_Ioi (fun t => rayF x₀ b c p t) 0 hl
  have e : ∀ t : ℝ, rayF x₀ b c ((l : ℂ) * p) t = rayF x₀ b c p (l * t) := by
    intro t; simp only [rayF]; push_cast; ring_nf
  simp_rw [e]
  rw [h, mul_zero, Complex.real_smul]
  have hl' : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
  push_cast
  field_simp

lemma deriv_rayInt_p (hx₀ : 0 < x₀) (hp : 0 < p.re) (hc : 0 < (c * p).re) :
    deriv (fun p => rayInt x₀ b c p) p = 0 := by
  set f := fun p => rayInt x₀ b c p
  have hd : HasDerivAt f (deriv f p) (((1 : ℝ) : ℂ) * p) := by
    rw [Complex.ofReal_one, one_mul]; exact (differentiableAt_rayInt_p hx₀ hp hc).hasDerivAt
  have hl : HasDerivAt (fun l : ℝ => (l : ℂ) * p) p 1 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (1 : ℝ))).mul_const p
  have h1 := hd.comp (1 : ℝ) hl
  have h2 : HasDerivAt (f ∘ fun l : ℝ => (l : ℂ) * p) 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (f p)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with l hl
    exact rayInt_ofReal_mul x₀ b c p hl
  have := h1.unique h2
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  exact (mul_eq_zero.1 this).resolve_right hp0

/-- The admissible directions for `c`. -/
def dirSet (c : ℂ) : Set ℂ := {p | 0 < p.re ∧ 0 < (c * p).re}

lemma isOpen_dirSet (c : ℂ) : IsOpen (dirSet c) := by
  have e : dirSet c = {p : ℂ | 0 < p.re} ∩ {p | 0 < (c * p).re} := rfl
  rw [e]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const (by fun_prop : Continuous fun p : ℂ => (c * p).re))

lemma convex_dirSet (c : ℂ) : Convex ℝ (dirSet c) := by
  have hlin : IsLinearMap ℝ fun p : ℂ => (c * p).re :=
    ⟨fun x y => by simp [mul_add], fun r x => by simp; ring⟩
  exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_gt hlin 0)

/-- **Contour rotation**: `Φ(c, p)` does not depend on the admissible direction `p`. -/
theorem rayInt_eq_of_mem (hx₀ : 0 < x₀) {p p' : ℂ} (hp : p ∈ dirSet c) (hp' : p' ∈ dirSet c) :
    rayInt x₀ b c p = rayInt x₀ b c p' :=
  (isOpen_dirSet c).is_const_of_deriv_eq_zero (convex_dirSet c).isPreconnected
    (fun _ hq => (differentiableAt_rayInt_p hx₀ hq.1 hq.2).differentiableWithinAt)
    (fun _ hq => deriv_rayInt_p hx₀ hq.1 hq.2) hp hp'

end Ray

/-! ### `D(c, w)` on the slit plane -/

/-- The direction `p(c) = 1 - i Im c/(|c| + Re c)`; `Re(c p(c)) = |c|`. -/
noncomputable def slitDir (c : ℂ) : ℂ := 1 - Complex.I * ((c.im / (‖c‖ + c.re) : ℝ) : ℂ)

lemma norm_add_re_pos {c : ℂ} (hc : c ∈ Complex.slitPlane) : 0 < ‖c‖ + c.re := by
  rcases Complex.mem_slitPlane_iff.1 hc with h | h
  · positivity
  · have := Complex.abs_re_lt_norm.2 h
    linarith [neg_abs_le c.re]

lemma slitDir_re (c : ℂ) : (slitDir c).re = 1 := by
  simp only [slitDir, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma re_mul_slitDir {c : ℂ} (hc : c ∈ Complex.slitPlane) : (c * slitDir c).re = ‖c‖ := by
  have hpos := norm_add_re_pos hc
  have hsq : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [slitDir, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    Complex.one_im]
  field_simp
  nlinarith [hsq]

lemma slitDir_mem {c : ℂ} (hc : c ∈ Complex.slitPlane) : slitDir c ∈ dirSet c :=
  ⟨by rw [slitDir_re]; norm_num, by rw [re_mul_slitDir hc]; exact norm_pos_iff.2 (Complex.slitPlane_ne_zero hc)⟩

/-- **`D(c, w)` on the slit plane**: `Φ(c, p(c))` with `x₀ = 1/u₀`, `b = -w - 1/2`. -/
noncomputable def Dslit (c : ℂ) (u₀ : ℝ) (w : ℂ) : ℂ := rayInt u₀⁻¹ (-w - 1 / 2) c (slitDir c)

section Dslit

variable {u₀ : ℝ}

lemma Dslit_eq_rayInt (hu₀ : 0 < u₀) {c p : ℂ} (hc : c ∈ Complex.slitPlane) (hp : p ∈ dirSet c)
    (w : ℂ) : Dslit c u₀ w = rayInt u₀⁻¹ (-w - 1 / 2) c p :=
  rayInt_eq_of_mem (inv_pos.2 hu₀) (slitDir_mem hc) hp

/-- The neighbourhood of `c₀` on which `D(c, w) = Φ(c, p(c₀))`. -/
lemma exists_ball_Dslit (hu₀ : 0 < u₀) {c₀ : ℂ} (hc₀ : c₀ ∈ Complex.slitPlane) :
    ∃ r > 0, r ≤ rayRad c₀ (slitDir c₀) ∧ ∀ c ∈ ball c₀ r, c ∈ Complex.slitPlane ∧
      ∀ w, Dslit c u₀ w = rayInt u₀⁻¹ (-w - 1 / 2) c (slitDir c₀) := by
  have hp₀ : 0 < (slitDir c₀).re := by rw [slitDir_re]; norm_num
  have hc₀' : 0 < (c₀ * slitDir c₀).re := (slitDir_mem hc₀).2
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 Complex.isOpen_slitPlane c₀ hc₀
  have hrr := rayRad_pos hp₀ hc₀'
  refine ⟨min ε (rayRad c₀ (slitDir c₀)), lt_min hε hrr, min_le_right _ _, fun c hc => ?_⟩
  have hcs : c ∈ Complex.slitPlane := hεs (ball_subset_ball (min_le_left _ _) hc)
  refine ⟨hcs, fun w => Dslit_eq_rayInt hu₀ hcs ⟨hp₀, ?_⟩ w⟩
  rw [mem_ball, dist_eq_norm] at hc
  have hc' : ‖c - c₀‖ < rayRad c₀ (slitDir c₀) := lt_of_lt_of_le hc (min_le_right _ _)
  have hp0 : ‖slitDir c₀ - slitDir c₀‖ < rayRad c₀ (slitDir c₀) := by
    rw [sub_self, norm_zero]; exact hrr
  have := (rayRad_props hp₀ hc₀' hc' hp0).2.1
  linarith

/-- **`D(·, w)` is holomorphic on the slit plane.** -/
theorem differentiableOn_Dslit (hu₀ : 0 < u₀) (w : ℂ) :
    DifferentiableOn ℂ (fun c => Dslit c u₀ w) Complex.slitPlane := by
  intro c₀ hc₀
  obtain ⟨r, hr, -, hball⟩ := exists_ball_Dslit hu₀ hc₀
  have hp₀ : 0 < (slitDir c₀).re := by rw [slitDir_re]; norm_num
  have hd := differentiableAt_rayInt_c (b := -w - 1 / 2) (inv_pos.2 hu₀) hp₀ (slitDir_mem hc₀).2
  have heq : (fun c => Dslit c u₀ w) =ᶠ[𝓝 c₀] fun c => rayInt u₀⁻¹ (-w - 1 / 2) c (slitDir c₀) :=
    Filter.eventually_of_mem (ball_mem_nhds c₀ hr) fun c hc => (hball c hc).2 w
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Substitution `t = 1/u - 1/u₀`: the ray integral along `[x₀, ∞)` is `lowerDualC`. -/
lemma rayInt_one_eq_lowerDualC (hu₀ : 0 < u₀) (c w : ℂ) :
    rayInt u₀⁻¹ (-w - 1 / 2) c 1 = lowerDualC c u₀ w := by
  set x₀ := u₀⁻¹
  have hx₀ : 0 < x₀ := inv_pos.2 hu₀
  set φ : ℝ → ℝ := fun u => u⁻¹ - x₀
  have himage : φ '' Ioo 0 u₀ = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      simp only [φ, mem_Ioi, sub_pos, x₀]
      exact inv_strictAnti₀ hu0 hu1
    · intro hy
      have hy : 0 < y := hy
      refine ⟨(y + x₀)⁻¹, ⟨by positivity, ?_⟩, ?_⟩
      · rw [inv_lt_comm₀ (by positivity) hu₀]; linarith
      · simp only [φ, inv_inv]; ring
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) u₀, HasDerivWithinAt φ (-(u ^ 2)⁻¹) (Ioo 0 u₀) u :=
    fun u hu => ((hasDerivAt_inv hu.1.ne').sub_const x₀).hasDerivWithinAt
  have hinj : InjOn φ (Ioo 0 u₀) := fun u _ v _ h => by
    simp only [φ, sub_left_inj, inv_inj] at h; exact h
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (rayF x₀ (-w - 1 / 2) c 1)
  rw [himage] at hcov
  unfold rayInt lowerDualC
  rw [one_mul, hcov, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hu0 : 0 < u := hu.1
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu0.ne'
  have hv : (x₀ : ℂ) + ((φ u : ℝ) : ℂ) * 1 = (u : ℂ)⁻¹ := by
    simp only [φ]; push_cast; ring
  have harg : Complex.arg (u : ℂ) ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hu0.le]; exact Real.pi_pos.ne
  have hpow : ((u : ℂ)⁻¹) ^ (-w - 1 / 2) = (u : ℂ) ^ (w + 1 / 2) := by
    rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]; ring_nf
  have hsplit : (u : ℂ) ^ (w + 1 / 2) = (u : ℂ) ^ (w - 1) * (u : ℂ) ^ (-(1 / 2) : ℂ) * (u : ℂ) ^ 2 := by
    rw [← Complex.cpow_add _ _ hu', ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hu']
    ring_nf
  have hhalf : (((u ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) = (u : ℂ) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_cpow hu0.le]; push_cast; ring_nf
  simp only [rayF, dualWC]
  rw [hv, hpow, hsplit, hhalf, abs_neg, abs_of_pos (by positivity : 0 < (u ^ 2)⁻¹),
    Complex.real_smul]
  push_cast
  rw [div_eq_mul_inv c]
  field_simp

/-- **Agreement**: `D(c, w) = lowerDualC c u₀ w` for `Re c > 0`. -/
theorem Dslit_eq_lowerDualC (hu₀ : 0 < u₀) {c : ℂ} (hc : 0 < c.re) (w : ℂ) :
    Dslit c u₀ w = lowerDualC c u₀ w := by
  have hcs : c ∈ Complex.slitPlane := Or.inl hc
  rw [Dslit_eq_rayInt hu₀ hcs (p := 1) ⟨by norm_num, by simpa using hc⟩,
    rayInt_one_eq_lowerDualC hu₀]

end Dslit

/-! ### `J^{(0)}_s(c)` and `J^{(1)}_{s+1}(c)` on the slit plane -/

section Jslit

variable {a : ℕ → ℂ} {R : ℝ} {u₀ : ℝ}

/-- Local bound: near `c₀`, `‖D(c, w)‖ ≤ K e^{π|Im w|} u₀^{Re w + 1/2}` whenever `Re w ≥ -1/2`. -/
lemma Dslit_local_bound (hu₀ : 0 < u₀) {c₀ : ℂ} (hc₀ : c₀ ∈ Complex.slitPlane) :
    ∃ r > 0, ball c₀ r ⊆ Complex.slitPlane ∧ ∃ K, 0 ≤ K ∧ ∀ c ∈ ball c₀ r, ∀ w : ℂ,
      -(1 / 2) ≤ w.re → ‖Dslit c u₀ w‖ ≤ K * rexp (π * |w.im|) * u₀ ^ (w.re + 1 / 2) := by
  obtain ⟨r, hr, hrr, hball⟩ := exists_ball_Dslit hu₀ hc₀
  set p₀ := slitDir c₀
  set x₀ := u₀⁻¹
  have hx₀ : 0 < x₀ := inv_pos.2 hu₀
  have hp₀ : 0 < p₀.re := by rw [slitDir_re]; norm_num
  have hc₀' : 0 < (c₀ * p₀).re := (slitDir_mem hc₀).2
  set κ := (c₀ * p₀).re / 2
  have hκ : 0 < κ := by positivity
  set E := ∫ t in Ioi (0 : ℝ), rexp (-(κ * t))
  have hEint : IntegrableOn (fun t : ℝ => rexp (-(κ * t))) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 hκ
    have e : (fun t : ℝ => rexp (-(κ * t))) = fun t => rexp (-κ * t) := by funext t; ring_nf
    rw [e]; exact this
  have hE : 0 ≤ E := setIntegral_nonneg measurableSet_Ioi fun t _ => (Real.exp_pos _).le
  refine ⟨r, hr, fun c hc => (hball c hc).1, ‖p₀‖ * rexp (x₀ * (‖c₀‖ + 1)) * (2 * E),
    by positivity, fun c hc w hw => ?_⟩
  rw [(hball c hc).2 w]
  set b := -w - 1 / 2
  have hbre : b.re = -w.re - 1 / 2 := by simp [b]
  have hbim : |b.im| = |w.im| := by simp [b]
  have hβ : b.re ≤ 0 := by rw [hbre]; linarith
  rw [mem_ball, dist_eq_norm] at hc
  have hc' : ‖c - c₀‖ < rayRad c₀ p₀ := lt_of_lt_of_le hc hrr
  have hp0 : ‖p₀ - p₀‖ < rayRad c₀ p₀ := by
    rw [sub_self, norm_zero]; exact rayRad_pos hp₀ hc₀'
  set Kb := rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))
  have hdomint := integrableOn_domF hx₀ b.re (q := ‖p₀‖ + 1) (by positivity) hκ
  have hint : ‖∫ t in Ioi (0 : ℝ), rayF x₀ b c p₀ t‖ ≤
      ∫ t in Ioi (0 : ℝ), Kb * domF x₀ b.re (‖p₀‖ + 1) κ t :=
    norm_integral_le_of_norm_le (hdomint.const_mul Kb)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
        norm_rayF_le_dom hx₀ hp₀ hc₀' hc' hp0 (le_of_lt ht)))
  rw [integral_const_mul] at hint
  have hdom : ∫ t in Ioi (0 : ℝ), domF x₀ b.re (‖p₀‖ + 1) κ t ≤ 2 * x₀ ^ b.re * E := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hdomint (hEint.const_mul _) measurableSet_Ioi fun t ht => ?_
    unfold domF
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    have h1 : (x₀ + t * (‖p₀‖ + 1)) ^ b.re ≤ x₀ ^ b.re :=
      Real.rpow_le_rpow_of_nonpos hx₀ (by nlinarith [norm_nonneg p₀]) hβ
    nlinarith [mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(κ * t))).le]
  have hx : x₀ ^ b.re = u₀ ^ (w.re + 1 / 2) := by
    rw [hbre, Real.inv_rpow hu₀.le, ← Real.rpow_neg hu₀.le]; ring_nf
  unfold rayInt
  rw [norm_mul]
  have hKb : 0 ≤ Kb := by positivity
  calc ‖p₀‖ * ‖∫ t in Ioi (0 : ℝ), rayF x₀ b c p₀ t‖
      ≤ ‖p₀‖ * (Kb * (2 * x₀ ^ b.re * E)) :=
        mul_le_mul_of_nonneg_left (hint.trans (mul_le_mul_of_nonneg_left hdom hKb)) (norm_nonneg _)
    _ = _ := by rw [hx]; simp only [Kb, hbim]; ring

/-- `∑ ‖a_n‖ ‖1/Γ((s+n)/2)‖ u₀^{Re (s+n)/2} < ∞`. -/
lemma summable_gammaWeight (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) (s : ℂ) :
    Summable fun n : ℕ => ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * u₀ ^ ((s + n) / 2).re := by
  obtain ⟨N, b, hb, hbn⟩ := hSeries_local_bound ha hR hu₀ (s - 2)
  have e : ∀ n : ℕ, ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * u₀ ^ ((s + n) / 2).re =
      u₀ * ‖hSeriesTerm a u₀ n (s - 2)‖ := by
    intro n
    unfold hSeriesTerm
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu₀,
      show (s - 2 + n) / 2 + 1 = (s + n) / 2 by ring,
      show ((s - 2 + n) / 2).re = ((s + n) / 2).re - 1 by simp; ring,
      Real.rpow_sub_one hu₀.ne']
    field_simp
  have hs : Summable fun n : ℕ => ‖hSeriesTerm a u₀ n (s - 2)‖ := by
    refine Summable.of_norm_bounded_eventually hb ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [norm_norm]
    exact hbn n hn (s - 2) (mem_ball_self one_pos)
  exact (hs.mul_left u₀).congr fun n => (e n).symm

/-- `J^{(0)}_s(c) = ∑ a_n/Γ((s+n)/2) D(c, (s+n)/2)` on the slit plane. -/
noncomputable def JslitE (a : ℕ → ℂ) (u₀ : ℝ) (s c : ℂ) : ℂ :=
  ∑' n : ℕ, a n * (Complex.Gamma ((s + n) / 2))⁻¹ * Dslit c u₀ ((s + n) / 2)

/-- `J^{(1)}_{s+1}(c) = ∑ a_n/Γ((s+1+n)/2) D(c, (s+1+n)/2 - 1)` on the slit plane. -/
noncomputable def JslitO (a : ℕ → ℂ) (u₀ : ℝ) (s c : ℂ) : ℂ :=
  ∑' n : ℕ, a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹ * Dslit c u₀ ((s + 1 + n) / 2 - 1)

/-- `JslitE` is the dual integral `J^{(0)}_s(c)` for `Re c > 0`. -/
theorem JslitE_eq (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) {c : ℂ} (hc : 0 < c.re)
    (s : ℂ) : JslitE a u₀ s c = geoJC (kernel a s) u₀ (1 / 2) c := by
  rw [← (hasSum_dSeriesC ha hR hc hu₀ s).tsum_eq]
  unfold JslitE dSeriesTermC
  simp_rw [Dslit_eq_lowerDualC hu₀ hc]

/-- `JslitO` is the dual integral `J^{(1)}_{s+1}(c)` for `Re c > 0`. -/
theorem JslitO_eq (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) {c : ℂ} (hc : 0 < c.re)
    (s : ℂ) : JslitO a u₀ s c = geoJC (kernel a (s + 1)) u₀ (3 / 2) c := by
  rw [← (hasSum_dSeriesOddC ha hR hc hu₀ s).tsum_eq]
  unfold JslitO dSeriesTermOddC
  simp_rw [Dslit_eq_lowerDualC hu₀ hc]

lemma half_re_ge {s : ℂ} {n : ℕ} (hn : ⌈|s.re|⌉₊ + 1 ≤ n) : -(1 / 2) ≤ ((s + n) / 2).re ∧
    -(1 / 2) ≤ ((s + 1 + n) / 2 - 1).re := by
  have h1 : |s.re| ≤ ⌈|s.re|⌉₊ := Nat.le_ceil _
  have h2 : ((⌈|s.re|⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h2
  have h3 := neg_abs_le s.re
  constructor <;> simp <;> linarith

/-- **`J^{(0)}_s` is holomorphic on the slit plane.** -/
theorem differentiableOn_JslitE (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) (s : ℂ) :
    DifferentiableOn ℂ (JslitE a u₀ s) Complex.slitPlane := by
  intro c₀ hc₀
  obtain ⟨r, hr, hsub, K, hK, hbd⟩ := Dslit_local_bound hu₀ hc₀
  have hd := differentiableAt_tsum_of_local_bound hr
    (T := fun n c => a n * (Complex.Gamma ((s + n) / 2))⁻¹ * Dslit c u₀ ((s + n) / 2))
    (fun n => ((differentiableOn_Dslit hu₀ _).mono hsub).const_mul _)
    ((summable_gammaWeight ha hR hu₀ s).mul_left (K * rexp (π * |s.im / 2|) * u₀ ^ (1 / 2 : ℝ)))
    (N := ⌈|s.re|⌉₊ + 1) (fun n hn c hc => ?_)
  · exact hd.differentiableWithinAt
  · have hw := (half_re_ge hn).1
    have hD := hbd c hc _ hw
    have him : ((s + n) / 2).im = s.im / 2 := by simp
    rw [him, Real.rpow_add hu₀] at hD
    rw [norm_mul, norm_mul]
    have h0 : 0 ≤ ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ := by positivity
    calc ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ‖Dslit c u₀ ((s + n) / 2)‖
        ≤ ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
          (K * rexp (π * |s.im / 2|) * (u₀ ^ ((s + n) / 2).re * u₀ ^ (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hD h0
      _ = _ := by ring

/-- **`J^{(1)}_{s+1}` is holomorphic on the slit plane.** -/
theorem differentiableOn_JslitO (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) (s : ℂ) :
    DifferentiableOn ℂ (JslitO a u₀ s) Complex.slitPlane := by
  intro c₀ hc₀
  obtain ⟨r, hr, hsub, K, hK, hbd⟩ := Dslit_local_bound hu₀ hc₀
  have hd := differentiableAt_tsum_of_local_bound hr
    (T := fun n c => a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹ * Dslit c u₀ ((s + 1 + n) / 2 - 1))
    (fun n => ((differentiableOn_Dslit hu₀ _).mono hsub).const_mul _)
    ((summable_gammaWeight ha hR hu₀ (s + 1)).mul_left
      (K * rexp (π * |s.im / 2|) * u₀ ^ (-(1 / 2) : ℝ)))
    (N := ⌈|s.re|⌉₊ + 1) (fun n hn c hc => ?_)
  · exact hd.differentiableWithinAt
  · have hw := (half_re_ge hn).2
    have hD := hbd c hc _ hw
    have him : ((s + 1 + n) / 2 - 1).im = s.im / 2 := by simp
    have hre : ((s + 1 + n) / 2 - 1).re + 1 / 2 = ((s + 1 + n) / 2).re + -(1 / 2) := by
      simp; ring
    rw [him, hre, Real.rpow_add hu₀] at hD
    rw [norm_mul, norm_mul]
    have h0 : 0 ≤ ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ := by positivity
    calc ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ * ‖Dslit c u₀ ((s + 1 + n) / 2 - 1)‖
        ≤ ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ *
          (K * rexp (π * |s.im / 2|) * (u₀ ^ ((s + 1 + n) / 2).re * u₀ ^ (-(1 / 2) : ℝ))) :=
          mul_le_mul_of_nonneg_left hD h0
      _ = _ := by ring

end Jslit

/-! ### Rays into the lower half-plane: the boundary values on the cut

For `p` with `Im p < 0` the ray `x₀ + tp` (`t ≥ 0`) stays in the slit plane (it never meets
`(-∞, 0]`) and keeps the distance `x₀ |Im p|/|p|` from `0`.  Such rays are admissible for `c` on
the negative real axis (e.g. `p = -1 - i`, `Re(cp) = -Re c + Im c`), and give the boundary value of
`D(·, w)` from `Im c > 0`. -/

section RayLow

variable {x₀ : ℝ} {b c p : ℂ} {t : ℝ}

lemma rayL_mem_slitPlane (hx₀ : 0 < x₀) (hp : p.im < 0) (ht : 0 ≤ t) :
    (x₀ : ℂ) + t * p ∈ Complex.slitPlane := by
  rcases ht.lt_or_eq with ht | ht
  · right; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_add, zero_mul, add_zero]
    exact (mul_neg_of_pos_of_neg ht hp).ne
  · left; subst ht; simpa using hx₀

lemma rayL_norm_ge (hx₀ : 0 ≤ x₀) :
    x₀ * |p.im| ≤ ‖(x₀ : ℂ) + t * p‖ * ‖p‖ := by
  have e : (((x₀ : ℂ) + t * p) * (starRingEnd ℂ) p).im = -(x₀ * p.im) := by
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have := Complex.abs_im_le_norm (((x₀ : ℂ) + t * p) * (starRingEnd ℂ) p)
  rw [e, norm_mul, Complex.norm_conj, abs_neg, abs_mul, abs_of_nonneg hx₀] at this
  exact this

lemma norm_cpow_le_of_ne_zero {v : ℂ} (hv : v ≠ 0) (b : ℂ) :
    ‖v ^ b‖ ≤ ‖v‖ ^ b.re * rexp (π * |b.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hv, div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  have := Complex.abs_arg_le_pi v
  calc -(Complex.arg v * b.im) ≤ |Complex.arg v * b.im| := neg_le_abs _
    _ = |Complex.arg v| * |b.im| := abs_mul _ _
    _ ≤ π * |b.im| := mul_le_mul_of_nonneg_right this (abs_nonneg _)

/-- Pointwise bound, with a lower bound `A ≤ |x₀ + tp|`. -/
lemma norm_rayF_le_of_ge (hx₀ : 0 < x₀) {A : ℝ} (hA : 0 < A) (hAv : A ≤ ‖(x₀ : ℂ) + t * p‖)
    {q : ℝ} (hq : ‖p‖ ≤ q) (ht : 0 ≤ t) :
    ‖rayF x₀ b c p t‖ ≤ rexp (π * |b.im|) * (A ^ b.re + (x₀ + t * q) ^ b.re) *
      (rexp (-(x₀ * c.re)) * rexp (-((c * p).re * t))) := by
  have hv0 : (x₀ : ℂ) + t * p ≠ 0 := fun h => by rw [h, norm_zero] at hAv; linarith
  unfold rayF
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, re_mul_ray, ← Real.exp_add]
  have h1 := norm_cpow_le_of_ne_zero hv0 b
  have h2 := rpow_le_add_of_mem (β := b.re) hA hAv (ray_norm_le hx₀.le hq ht)
  have e : -(x₀ * c.re + t * (c * p).re) = -(x₀ * c.re) + -((c * p).re * t) := by ring
  rw [e]
  have hE := (Real.exp_pos (-(x₀ * c.re) + -((c * p).re * t))).le
  calc ‖((x₀ : ℂ) + t * p) ^ b‖ * rexp (-(x₀ * c.re) + -((c * p).re * t))
      ≤ (‖(x₀ : ℂ) + t * p‖ ^ b.re * rexp (π * |b.im|)) *
          rexp (-(x₀ * c.re) + -((c * p).re * t)) := mul_le_mul_of_nonneg_right h1 hE
    _ ≤ ((A ^ b.re + (x₀ + t * q) ^ b.re) * rexp (π * |b.im|)) *
          rexp (-(x₀ * c.re) + -((c * p).re * t)) := by gcongr
    _ = _ := by ring

/-- `(A^β + (x₀ + tq)^β) e^{-κt}`. -/
noncomputable def domL (A x₀ β q κ : ℝ) (t : ℝ) : ℝ :=
  (A ^ β + (x₀ + t * q) ^ β) * rexp (-(κ * t))

lemma domL_eq (A x₀ β q κ t : ℝ) :
    domL A x₀ β q κ t = domF x₀ β q κ t + (A ^ β - x₀ ^ β) * rexp (-(κ * t)) := by
  unfold domL domF; ring

lemma integrableOn_domL (hx₀ : 0 < x₀) (A β : ℝ) {q κ : ℝ} (hq : 0 < q) (hκ : 0 < κ) :
    IntegrableOn (domL A x₀ β q κ) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => (A ^ β - x₀ ^ β) * rexp (-(κ * t))) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 hκ).const_mul (A ^ β - x₀ ^ β)
    have e : (fun t : ℝ => (A ^ β - x₀ ^ β) * rexp (-(κ * t))) =
        fun t => (A ^ β - x₀ ^ β) * rexp (-κ * t) := by funext t; ring_nf
    rw [e]; exact this
  exact ((integrableOn_domF hx₀ β hq hκ).add h1).congr_fun
    (fun t _ => by simp only [Pi.add_apply]; rw [domL_eq]) measurableSet_Ioi

lemma continuousOn_rayF_low (hx₀ : 0 < x₀) (hp : p.im < 0) :
    ContinuousOn (rayF x₀ b c p) (Ici 0) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  have hv : ContinuousAt (fun t : ℝ => (x₀ : ℂ) + t * p) t := by fun_prop
  exact (hv.cpow continuousAt_const (rayL_mem_slitPlane hx₀ hp ht)).mul (by fun_prop)

lemma aestronglyMeasurable_rayF_low (hx₀ : 0 < x₀) (hp : p.im < 0) :
    AEStronglyMeasurable (rayF x₀ b c p) (volume.restrict (Ioi 0)) :=
  ((continuousOn_rayF_low hx₀ hp).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi

/-- The radius of a common neighbourhood of `(c₀, p₀)`, `Im p₀ < 0`. -/
noncomputable def rayRadL (c₀ p₀ : ℂ) : ℝ :=
  min (min 1 (-p₀.im / 2)) ((c₀ * p₀).re / (2 * (‖c₀‖ + ‖p₀‖ + 1)))

lemma rayRadL_pos {c₀ p₀ : ℂ} (hp₀ : p₀.im < 0) (hc₀ : 0 < (c₀ * p₀).re) : 0 < rayRadL c₀ p₀ := by
  unfold rayRadL
  have : 0 < -p₀.im / 2 := by linarith
  positivity

lemma rayRadL_props {c₀ p₀ c p : ℂ} (hc : ‖c - c₀‖ < rayRadL c₀ p₀)
    (hp : ‖p - p₀‖ < rayRadL c₀ p₀) :
    p.im ≤ p₀.im / 2 ∧ (c₀ * p₀).re / 2 ≤ (c * p).re ∧ ‖p‖ ≤ ‖p₀‖ + 1 ∧ ‖c‖ ≤ ‖c₀‖ + 1 := by
  set r := rayRadL c₀ p₀
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ -p₀.im / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ (c₀ * p₀).re / (2 * (‖c₀‖ + ‖p₀‖ + 1)) := min_le_right _ _
  have hpn : ‖p‖ ≤ ‖p₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' p p₀; linarith
  have hcn : ‖c‖ ≤ ‖c₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c c₀; linarith
  refine ⟨?_, ?_, hpn, hcn⟩
  · have := Complex.abs_im_le_norm (p - p₀)
    rw [Complex.sub_im] at this
    linarith [le_abs_self (p.im - p₀.im)]
  · have e : c * p - c₀ * p₀ = (c - c₀) * p + c₀ * (p - p₀) := by ring
    have hn : ‖c * p - c₀ * p₀‖ ≤ r * (‖c₀‖ + ‖p₀‖ + 1) := by
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖c - c₀‖ * ‖p‖ ≤ r * (‖p₀‖ + 1) :=
        mul_le_mul hc.le hpn (norm_nonneg _) (le_trans (norm_nonneg _) hc.le)
      have h2 : ‖c₀‖ * ‖p - p₀‖ ≤ ‖c₀‖ * r := mul_le_mul_of_nonneg_left hp.le (norm_nonneg _)
      linarith
    have hpos : (0 : ℝ) < 2 * (‖c₀‖ + ‖p₀‖ + 1) := by positivity
    have hr3' : r * (‖c₀‖ + ‖p₀‖ + 1) ≤ (c₀ * p₀).re / 2 := by
      rw [le_div_iff₀ hpos] at hr3
      linarith
    have := Complex.abs_re_le_norm (c * p - c₀ * p₀)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le ((c * p).re - (c₀ * p₀).re)]

/-- The lower bound `A = x₀ |Im p₀| / (2(|p₀| + 1))` for `|x₀ + tp|` near `p₀`. -/
noncomputable def lowA (x₀ : ℝ) (p₀ : ℂ) : ℝ := x₀ * (-p₀.im / 2) / (‖p₀‖ + 1)

lemma lowA_pos (hx₀ : 0 < x₀) {p₀ : ℂ} (hp₀ : p₀.im < 0) : 0 < lowA x₀ p₀ := by
  unfold lowA
  have : 0 < -p₀.im / 2 := by linarith
  positivity

lemma lowA_le_x₀ (hx₀ : 0 < x₀) {p₀ : ℂ} (hp₀ : p₀.im < 0) : lowA x₀ p₀ ≤ x₀ := by
  unfold lowA
  rw [div_le_iff₀ (by positivity)]
  have h1 := Complex.abs_im_le_norm p₀
  rw [abs_of_neg hp₀] at h1
  nlinarith

lemma lowA_le_norm (hx₀ : 0 < x₀) {c₀ p₀ c p : ℂ} (hp₀ : p₀.im < 0)
    (hc : ‖c - c₀‖ < rayRadL c₀ p₀) (hp : ‖p - p₀‖ < rayRadL c₀ p₀) :
    lowA x₀ p₀ ≤ ‖(x₀ : ℂ) + t * p‖ := by
  obtain ⟨h1, -, h3, -⟩ := rayRadL_props hc hp
  have hpim : p.im < 0 := by linarith
  have hge := rayL_norm_ge (p := p) (t := t) hx₀.le
  rw [abs_of_neg hpim] at hge
  unfold lowA
  rw [div_le_iff₀ (by positivity)]
  have hv := norm_nonneg ((x₀ : ℂ) + t * p)
  calc x₀ * (-p₀.im / 2) ≤ x₀ * -p.im := by nlinarith
    _ ≤ ‖(x₀ : ℂ) + t * p‖ * ‖p‖ := hge
    _ ≤ ‖(x₀ : ℂ) + t * p‖ * (‖p₀‖ + 1) := mul_le_mul_of_nonneg_left h3 hv

lemma norm_rayF_le_domL (hx₀ : 0 < x₀) {c₀ p₀ : ℂ} (hp₀ : p₀.im < 0)
    (hc : ‖c - c₀‖ < rayRadL c₀ p₀) (hp : ‖p - p₀‖ < rayRadL c₀ p₀) (ht : 0 ≤ t) :
    ‖rayF x₀ b c p t‖ ≤ (rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))) *
      domL (lowA x₀ p₀) x₀ b.re (‖p₀‖ + 1) ((c₀ * p₀).re / 2) t := by
  obtain ⟨h1, h2, h3, h4⟩ := rayRadL_props hc hp
  refine (norm_rayF_le_of_ge hx₀ (lowA_pos hx₀ hp₀) (lowA_le_norm hx₀ hp₀ hc hp) h3 ht).trans ?_
  have hA : rexp (-(x₀ * c.re)) ≤ rexp (x₀ * (‖c₀‖ + 1)) := by
    rw [Real.exp_le_exp]
    have := neg_abs_le c.re
    have := Complex.abs_re_le_norm c
    nlinarith
  have hB : rexp (-((c * p).re * t)) ≤ rexp (-((c₀ * p₀).re / 2 * t)) := by
    rw [Real.exp_le_exp]; nlinarith
  have hS : 0 ≤ lowA x₀ p₀ ^ b.re + (x₀ + t * (‖p₀‖ + 1)) ^ b.re := by
    have : 0 ≤ x₀ + t * (‖p₀‖ + 1) := by positivity
    have := (lowA_pos hx₀ hp₀).le
    positivity
  unfold domL
  calc rexp (π * |b.im|) * (lowA x₀ p₀ ^ b.re + (x₀ + t * (‖p₀‖ + 1)) ^ b.re) *
        (rexp (-(x₀ * c.re)) * rexp (-((c * p).re * t)))
      ≤ rexp (π * |b.im|) * (lowA x₀ p₀ ^ b.re + (x₀ + t * (‖p₀‖ + 1)) ^ b.re) *
        (rexp (x₀ * (‖c₀‖ + 1)) * rexp (-((c₀ * p₀).re / 2 * t))) := by gcongr
    _ = _ := by ring

theorem differentiableAt_rayInt_c_low (hx₀ : 0 < x₀) {c₀ p₀ : ℂ} (hp₀ : p₀.im < 0)
    (hc₀ : 0 < (c₀ * p₀).re) : DifferentiableAt ℂ (fun c => rayInt x₀ b c p₀) c₀ := by
  have hr := rayRadL_pos hp₀ hc₀
  have hp0 : ‖p₀ - p₀‖ < rayRadL c₀ p₀ := by rw [sub_self, norm_zero]; exact hr
  have hdom : IntegrableOn (fun t => (rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))) *
      domL (lowA x₀ p₀) x₀ b.re (‖p₀‖ + 1) ((c₀ * p₀).re / 2) t) (Ioi 0) :=
    (integrableOn_domL hx₀ _ b.re (by positivity) (by positivity)).const_mul _
  show DifferentiableAt ℂ (fun c => p₀ * ∫ t in Ioi (0 : ℝ), rayF x₀ b c p₀ t) c₀
  refine (differentiableAt_const p₀).mul ?_
  refine differentiableAt_integral_of_dominated (F := fun c t => rayF x₀ b c p₀ t) hr hdom
    (fun c _ => aestronglyMeasurable_rayF_low hx₀ hp₀) (Eventually.of_forall fun t => ?_) ?_
  · intro c _
    unfold rayF
    exact ((differentiableAt_const _).mul ((differentiableAt_id.mul
      (differentiableAt_const _)).neg.cexp)).differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht c hc => ?_)
    rw [mem_ball, dist_eq_norm] at hc
    exact norm_rayF_le_domL hx₀ hp₀ hc hp0 (le_of_lt ht)

theorem differentiableAt_rayInt_p_low (hx₀ : 0 < x₀) {c₀ p₀ : ℂ} (hp₀ : p₀.im < 0)
    (hc₀ : 0 < (c₀ * p₀).re) : DifferentiableAt ℂ (fun p => rayInt x₀ b c₀ p) p₀ := by
  have hr := rayRadL_pos hp₀ hc₀
  have hc0 : ‖c₀ - c₀‖ < rayRadL c₀ p₀ := by rw [sub_self, norm_zero]; exact hr
  have hdom : IntegrableOn (fun t => (rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))) *
      domL (lowA x₀ p₀) x₀ b.re (‖p₀‖ + 1) ((c₀ * p₀).re / 2) t) (Ioi 0) :=
    (integrableOn_domL hx₀ _ b.re (by positivity) (by positivity)).const_mul _
  show DifferentiableAt ℂ (fun p => p * ∫ t in Ioi (0 : ℝ), rayF x₀ b c₀ p t) p₀
  refine differentiableAt_id.mul ?_
  refine differentiableAt_integral_of_dominated (F := fun p t => rayF x₀ b c₀ p t) hr hdom
    (fun p hp => ?_) ?_ ?_
  · rw [mem_ball, dist_eq_norm] at hp
    exact aestronglyMeasurable_rayF_low hx₀ (by linarith [(rayRadL_props hc0 hp).1])
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht p hp => ?_)
    rw [mem_ball, dist_eq_norm] at hp
    have hpim : p.im < 0 := by linarith [(rayRadL_props hc0 hp).1]
    have hv : DifferentiableAt ℂ (fun p : ℂ => (x₀ : ℂ) + t * p) p := by fun_prop
    unfold rayF
    exact ((hv.cpow_const (rayL_mem_slitPlane hx₀ hpim (le_of_lt ht))).mul
      ((differentiableAt_const c₀).mul hv).neg.cexp).differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht p hp => ?_)
    rw [mem_ball, dist_eq_norm] at hp
    exact norm_rayF_le_domL hx₀ hp₀ hc0 hp (le_of_lt ht)

lemma deriv_rayInt_p_low (hx₀ : 0 < x₀) (hp : p.im < 0) (hc : 0 < (c * p).re) :
    deriv (fun p => rayInt x₀ b c p) p = 0 := by
  set f := fun p => rayInt x₀ b c p
  have hd : HasDerivAt f (deriv f p) (((1 : ℝ) : ℂ) * p) := by
    rw [Complex.ofReal_one, one_mul]; exact (differentiableAt_rayInt_p_low hx₀ hp hc).hasDerivAt
  have hl : HasDerivAt (fun l : ℝ => (l : ℂ) * p) p 1 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (1 : ℝ))).mul_const p
  have h1 := hd.comp (1 : ℝ) hl
  have h2 : HasDerivAt (f ∘ fun l : ℝ => (l : ℂ) * p) 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (f p)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with l hl
    exact rayInt_ofReal_mul x₀ b c p hl
  have := h1.unique h2
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  exact (mul_eq_zero.1 this).resolve_right hp0

/-- The admissible directions into the lower half-plane. -/
def dirLow (c : ℂ) : Set ℂ := {p | p.im < 0 ∧ 0 < (c * p).re}

lemma isOpen_dirLow (c : ℂ) : IsOpen (dirLow c) := by
  have e : dirLow c = {p : ℂ | p.im < 0} ∩ {p | 0 < (c * p).re} := rfl
  rw [e]
  exact (isOpen_lt Complex.continuous_im continuous_const).inter
    (isOpen_lt continuous_const (by fun_prop : Continuous fun p : ℂ => (c * p).re))

lemma convex_dirLow (c : ℂ) : Convex ℝ (dirLow c) := by
  have hlin : IsLinearMap ℝ fun p : ℂ => (c * p).re :=
    ⟨fun x y => by simp [mul_add], fun r x => by simp; ring⟩
  exact (convex_halfSpace_im_lt 0).inter (convex_halfSpace_gt hlin 0)

theorem rayInt_eq_of_mem_low (hx₀ : 0 < x₀) {p p' : ℂ} (hp : p ∈ dirLow c) (hp' : p' ∈ dirLow c) :
    rayInt x₀ b c p = rayInt x₀ b c p' :=
  (isOpen_dirLow c).is_const_of_deriv_eq_zero (convex_dirLow c).isPreconnected
    (fun _ hq => (differentiableAt_rayInt_p_low hx₀ hq.1 hq.2).differentiableWithinAt)
    (fun _ hq => deriv_rayInt_p_low hx₀ hq.1 hq.2) hp hp'

end RayLow

/-! ### The boundary value `D⁺(c, w)` from `Im c > 0` -/

/-- The direction `-1 - i`, admissible for `Re(c(-1-i)) = Im c - Re c > 0` (this includes the
negative real axis). -/
def pUp : ℂ := -1 - Complex.I

/-- The half-plane `Im c > Re c`, where `D⁺` is defined. -/
def upPlane : Set ℂ := {c | 0 < (c * pUp).re}

lemma pUp_im : pUp.im = -1 := by simp [pUp]

lemma re_mul_pUp (c : ℂ) : (c * pUp).re = c.im - c.re := by simp [pUp]; ring

lemma isOpen_upPlane : IsOpen upPlane :=
  isOpen_lt continuous_const (by fun_prop : Continuous fun c : ℂ => (c * pUp).re)

lemma neg_real_mem_upPlane {x : ℝ} (hx : x < 0) : (x : ℂ) ∈ upPlane := by
  show 0 < ((x : ℂ) * pUp).re
  rw [re_mul_pUp]; simp; linarith

/-- `D⁺(c, w) = Φ(c, -1 - i)` on `Im c > Re c`. -/
noncomputable def Dup (c : ℂ) (u₀ : ℝ) (w : ℂ) : ℂ := rayInt u₀⁻¹ (-w - 1 / 2) c pUp

section Dup

variable {u₀ : ℝ}

lemma slitDir_im_neg {c : ℂ} (hc : 0 < c.im) : (slitDir c).im < 0 := by
  have hpos := norm_add_re_pos (c := c) (Or.inr hc.ne')
  simp only [slitDir, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, zero_sub]
  exact neg_lt_zero.2 (div_pos hc hpos)

/-- **`D⁺` is `D` for `Im c > 0`** (rotating within the lower half-plane of directions). -/
theorem Dslit_eq_Dup (hu₀ : 0 < u₀) {c : ℂ} (hc : 0 < c.im) (hc' : c ∈ upPlane) (w : ℂ) :
    Dslit c u₀ w = Dup c u₀ w :=
  rayInt_eq_of_mem_low (inv_pos.2 hu₀)
    ⟨slitDir_im_neg hc, (slitDir_mem (Or.inr hc.ne')).2⟩ ⟨by rw [pUp_im]; norm_num, hc'⟩

theorem differentiableOn_Dup (hu₀ : 0 < u₀) (w : ℂ) :
    DifferentiableOn ℂ (fun c => Dup c u₀ w) upPlane := fun c₀ hc₀ =>
  (differentiableAt_rayInt_c_low (b := -w - 1 / 2) (inv_pos.2 hu₀)
    (by rw [pUp_im]; norm_num) hc₀).differentiableWithinAt

/-- Local bound for `D⁺`: `‖D⁺(c, w)‖ ≤ K e^{π|Im w|} (1/A)^{Re w + 1/2}` for `Re w ≥ -1/2`. -/
lemma Dup_local_bound (hu₀ : 0 < u₀) {c₀ : ℂ} (hc₀ : c₀ ∈ upPlane) :
    ∃ r > 0, ball c₀ r ⊆ upPlane ∧ ∃ K, 0 ≤ K ∧ ∃ L > 0, ∀ c ∈ ball c₀ r, ∀ w : ℂ,
      -(1 / 2) ≤ w.re → ‖Dup c u₀ w‖ ≤ K * rexp (π * |w.im|) * L ^ (w.re + 1 / 2) := by
  set p₀ := pUp
  set x₀ := u₀⁻¹
  have hx₀ : 0 < x₀ := inv_pos.2 hu₀
  have hp₀ : p₀.im < 0 := by simp only [p₀]; rw [pUp_im]; norm_num
  have hc₀' : 0 < (c₀ * p₀).re := hc₀
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 isOpen_upPlane c₀ hc₀
  have hrr := rayRadL_pos hp₀ hc₀'
  set r := min ε (rayRadL c₀ p₀)
  have hr : 0 < r := lt_min hε hrr
  set κ := (c₀ * p₀).re / 2
  have hκ : 0 < κ := by positivity
  set A := lowA x₀ p₀
  have hA := lowA_pos hx₀ hp₀
  have hAx := lowA_le_x₀ hx₀ hp₀
  set E := ∫ t in Ioi (0 : ℝ), rexp (-(κ * t))
  have hEint : IntegrableOn (fun t : ℝ => rexp (-(κ * t))) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 hκ
    have e : (fun t : ℝ => rexp (-(κ * t))) = fun t => rexp (-κ * t) := by funext t; ring_nf
    rw [e]; exact this
  have hE : 0 ≤ E := setIntegral_nonneg measurableSet_Ioi fun t _ => (Real.exp_pos _).le
  refine ⟨r, hr, (ball_subset_ball (min_le_left _ _)).trans hεs,
    ‖p₀‖ * rexp (x₀ * (‖c₀‖ + 1)) * (2 * E), by positivity, A⁻¹, inv_pos.2 hA,
    fun c hc w hw => ?_⟩
  set b := -w - 1 / 2
  have hbre : b.re = -w.re - 1 / 2 := by simp [b]
  have hbim : |b.im| = |w.im| := by simp [b]
  have hβ : b.re ≤ 0 := by rw [hbre]; linarith
  rw [mem_ball, dist_eq_norm] at hc
  have hc' : ‖c - c₀‖ < rayRadL c₀ p₀ := lt_of_lt_of_le hc (min_le_right _ _)
  have hp0 : ‖p₀ - p₀‖ < rayRadL c₀ p₀ := by rw [sub_self, norm_zero]; exact hrr
  set Kb := rexp (π * |b.im|) * rexp (x₀ * (‖c₀‖ + 1))
  have hdomint := integrableOn_domL hx₀ A b.re (q := ‖p₀‖ + 1) (by positivity) hκ
  have hint : ‖∫ t in Ioi (0 : ℝ), rayF x₀ b c p₀ t‖ ≤
      ∫ t in Ioi (0 : ℝ), Kb * domL A x₀ b.re (‖p₀‖ + 1) κ t :=
    norm_integral_le_of_norm_le (hdomint.const_mul Kb)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
        norm_rayF_le_domL hx₀ hp₀ hc' hp0 (le_of_lt ht)))
  rw [integral_const_mul] at hint
  have hdom : ∫ t in Ioi (0 : ℝ), domL A x₀ b.re (‖p₀‖ + 1) κ t ≤ 2 * A ^ b.re * E := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hdomint (hEint.const_mul _) measurableSet_Ioi fun t ht => ?_
    unfold domL
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    have h1 : (x₀ + t * (‖p₀‖ + 1)) ^ b.re ≤ A ^ b.re :=
      Real.rpow_le_rpow_of_nonpos hA (by nlinarith [norm_nonneg p₀]) hβ
    nlinarith [mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(κ * t))).le]
  have hx : A ^ b.re = A⁻¹ ^ (w.re + 1 / 2) := by
    rw [hbre, Real.inv_rpow hA.le, ← Real.rpow_neg hA.le]; congr 1; ring
  unfold Dup rayInt
  rw [norm_mul]
  have hKb : 0 ≤ Kb := by positivity
  calc ‖pUp‖ * ‖∫ t in Ioi (0 : ℝ), rayF x₀ b c pUp t‖
      ≤ ‖p₀‖ * (Kb * (2 * A ^ b.re * E)) :=
        mul_le_mul_of_nonneg_left (hint.trans (mul_le_mul_of_nonneg_left hdom hKb)) (norm_nonneg _)
    _ = _ := by rw [hx]; simp only [Kb, hbim]; ring

end Dup

section Jup

variable {a : ℕ → ℂ} {R : ℝ} {u₀ : ℝ}

/-- The boundary value `J^{(0)+}_s(c)` (from `Im c > 0`), defined on `Im c > Re c`. -/
noncomputable def JupE (a : ℕ → ℂ) (u₀ : ℝ) (s c : ℂ) : ℂ :=
  ∑' n : ℕ, a n * (Complex.Gamma ((s + n) / 2))⁻¹ * Dup c u₀ ((s + n) / 2)

/-- The boundary value `J^{(1)+}_{s+1}(c)` (from `Im c > 0`), defined on `Im c > Re c`. -/
noncomputable def JupO (a : ℕ → ℂ) (u₀ : ℝ) (s c : ℂ) : ℂ :=
  ∑' n : ℕ, a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹ * Dup c u₀ ((s + 1 + n) / 2 - 1)

theorem JslitE_eq_JupE (hu₀ : 0 < u₀) {c : ℂ} (hc : 0 < c.im) (hc' : c ∈ upPlane) (s : ℂ) :
    JslitE a u₀ s c = JupE a u₀ s c := by
  unfold JslitE JupE; simp_rw [Dslit_eq_Dup hu₀ hc hc']

theorem JslitO_eq_JupO (hu₀ : 0 < u₀) {c : ℂ} (hc : 0 < c.im) (hc' : c ∈ upPlane) (s : ℂ) :
    JslitO a u₀ s c = JupO a u₀ s c := by
  unfold JslitO JupO; simp_rw [Dslit_eq_Dup hu₀ hc hc']

theorem differentiableOn_JupE (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) (s : ℂ) :
    DifferentiableOn ℂ (JupE a u₀ s) upPlane := by
  intro c₀ hc₀
  obtain ⟨r, hr, hsub, K, hK, L, hL, hbd⟩ := Dup_local_bound hu₀ hc₀
  have hd := differentiableAt_tsum_of_local_bound hr
    (T := fun n c => a n * (Complex.Gamma ((s + n) / 2))⁻¹ * Dup c u₀ ((s + n) / 2))
    (fun n => ((differentiableOn_Dup hu₀ _).mono hsub).const_mul _)
    ((summable_gammaWeight ha hR hL s).mul_left (K * rexp (π * |s.im / 2|) * L ^ (1 / 2 : ℝ)))
    (N := ⌈|s.re|⌉₊ + 1) (fun n hn c hc => ?_)
  · exact hd.differentiableWithinAt
  · have hw := (half_re_ge hn).1
    have hD := hbd c hc _ hw
    have him : ((s + n) / 2).im = s.im / 2 := by simp
    rw [him, Real.rpow_add hL] at hD
    rw [norm_mul, norm_mul]
    have h0 : 0 ≤ ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ := by positivity
    calc ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ‖Dup c u₀ ((s + n) / 2)‖
        ≤ ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
          (K * rexp (π * |s.im / 2|) * (L ^ ((s + n) / 2).re * L ^ (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hD h0
      _ = _ := by ring

theorem differentiableOn_JupO (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) (s : ℂ) :
    DifferentiableOn ℂ (JupO a u₀ s) upPlane := by
  intro c₀ hc₀
  obtain ⟨r, hr, hsub, K, hK, L, hL, hbd⟩ := Dup_local_bound hu₀ hc₀
  have hd := differentiableAt_tsum_of_local_bound hr
    (T := fun n c => a n * (Complex.Gamma ((s + 1 + n) / 2))⁻¹ * Dup c u₀ ((s + 1 + n) / 2 - 1))
    (fun n => ((differentiableOn_Dup hu₀ _).mono hsub).const_mul _)
    ((summable_gammaWeight ha hR hL (s + 1)).mul_left
      (K * rexp (π * |s.im / 2|) * L ^ (-(1 / 2) : ℝ)))
    (N := ⌈|s.re|⌉₊ + 1) (fun n hn c hc => ?_)
  · exact hd.differentiableWithinAt
  · have hw := (half_re_ge hn).2
    have hD := hbd c hc _ hw
    have him : ((s + 1 + n) / 2 - 1).im = s.im / 2 := by simp
    have hre : ((s + 1 + n) / 2 - 1).re + 1 / 2 = ((s + 1 + n) / 2).re + -(1 / 2) := by
      simp; ring
    rw [him, hre, Real.rpow_add hL] at hD
    rw [norm_mul, norm_mul]
    have h0 : 0 ≤ ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ := by positivity
    calc ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ * ‖Dup c u₀ ((s + 1 + n) / 2 - 1)‖
        ≤ ‖a n‖ * ‖(Complex.Gamma ((s + 1 + n) / 2))⁻¹‖ *
          (K * rexp (π * |s.im / 2|) * (L ^ ((s + 1 + n) / 2).re * L ^ (-(1 / 2) : ℝ))) :=
          mul_le_mul_of_nonneg_left hD h0
      _ = _ := by ring

/-- `JupE` is the boundary value of `JslitE` from `Im c > 0`, in particular on the cut. -/
theorem tendsto_JslitE_JupE (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) (s : ℂ)
    {c₀ : ℂ} (hc₀ : c₀ ∈ upPlane) :
    Tendsto (JslitE a u₀ s) (𝓝[{c | 0 < c.im}] c₀) (𝓝 (JupE a u₀ s c₀)) := by
  have h := ((differentiableOn_JupE ha hR hu₀ s).continuousOn.continuousAt
    (isOpen_upPlane.mem_nhds hc₀)).tendsto.mono_left (nhdsWithin_le_nhds (s := {c | 0 < c.im}))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_upPlane.mem_nhds hc₀)] with c hc hc'
  exact (JslitE_eq_JupE hu₀ hc hc' s).symm

theorem tendsto_JslitO_JupO (ha : GeomBounded a R) (hR : 0 ≤ R) (hu₀ : 0 < u₀) (s : ℂ)
    {c₀ : ℂ} (hc₀ : c₀ ∈ upPlane) :
    Tendsto (JslitO a u₀ s) (𝓝[{c | 0 < c.im}] c₀) (𝓝 (JupO a u₀ s c₀)) := by
  have h := ((differentiableOn_JupO ha hR hu₀ s).continuousOn.continuousAt
    (isOpen_upPlane.mem_nhds hc₀)).tendsto.mono_left (nhdsWithin_le_nhds (s := {c | 0 < c.im}))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_upPlane.mem_nhds hc₀)] with c hc hc'
  exact (JslitO_eq_JupO hu₀ hc hc' s).symm

end Jup

end ZetaF
