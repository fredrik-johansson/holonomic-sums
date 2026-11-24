/-
# Boundary uniqueness (the reflection step in the proof of Theorem 4.1(1))

The proof of Theorem 4.1(1) continues an identity from the segment `0 < α < 1` into the upper
half-strip: the difference of the two sides is holomorphic for `Im α > 0`, continuous up to the
segment, and vanishes there.  The paper appeals to the reflection principle.  We prove what is
needed directly:

* `differentiableOn_ball_of_line` (Painlevé's theorem for a line): a function continuous on a disc
  and holomorphic off a horizontal line is holomorphic, via Morera's theorem
  (`isConservativeOn_and_continuousOn_iff_isDifferentiableOn`);
* `eqOn_zero_of_boundary`: a holomorphic function on a connected open set `U` which extends
  continuously by `0` to a segment of the real axis bounding `U` vanishes identically.
-/
import ZetaF.Deps
import Mathlib.Analysis.Complex.HasPrimitives

open Complex Set Metric Filter Topology
open scoped Interval

namespace ZetaF

/-- The integral of `f` around the boundary of the rectangle with corners `z`, `w`. -/
noncomputable def rectBdry (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

lemma rectBdry_split (f : ℂ → ℂ) (z w : ℂ) (b : ℝ)
    (h1 : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) MeasureTheory.volume z.im b)
    (h2 : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) MeasureTheory.volume b w.im)
    (h3 : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) MeasureTheory.volume z.im b)
    (h4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) MeasureTheory.volume b w.im) :
    rectBdry f z w = rectBdry f z (w.re + b * I) + rectBdry f (z.re + b * I) w := by
  simp only [rectBdry, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_im, add_im,
    mul_zero, sub_zero, mul_one, add_zero, zero_add, smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    ← intervalIntegral.integral_add_adjacent_intervals h3 h4]
  ring

lemma not_mem_Ioo_min_max (a b : ℝ) : b ∉ Ioo (min a b) (max a b) := by
  intro h
  simp only [Set.mem_Ioo, min_lt_iff, lt_max_iff, lt_irrefl, or_false] at h
  linarith [h.1, h.2]

lemma not_mem_Ioo_min_max' (a b : ℝ) : b ∉ Ioo (min b a) (max b a) := by
  rw [min_comm, max_comm]; exact not_mem_Ioo_min_max a b

/-- **Painlevé's theorem for a horizontal line.** -/
theorem differentiableOn_ball_of_line {f : ℂ → ℂ} {c : ℂ} {r b : ℝ}
    (hc : ContinuousOn f (ball c r)) (hd : DifferentiableOn ℂ f (ball c r \ {z | z.im = b})) :
    DifferentiableOn ℂ f (ball c r) := by
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_ball).1 ⟨?_, hc⟩
  -- rectangles whose interior misses the line
  have key : ∀ z w : ℂ, Rectangle z w ⊆ ball c r →
      b ∉ Ioo (min z.im w.im) (max z.im w.im) → rectBdry f z w = 0 := by
    intro z w hsub hb
    refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
      (hc.mono hsub) (hd.mono fun x hx => ⟨hsub ?_, fun hxb => hb (hxb ▸ hx.2)⟩)
    exact (inter_subset_inter (preimage_mono Ioo_subset_Icc_self)
      (preimage_mono Ioo_subset_Icc_self)) hx
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  change rectBdry f z w = 0
  by_cases hb : b ∈ Ioo (min z.im w.im) (max z.im w.im)
  · have hbI : b ∈ [[z.im, w.im]] := Ioo_subset_Icc_self hb
    have hvert : ∀ x ∈ [[z.re, w.re]], ∀ y₁ y₂ : ℝ, [[y₁, y₂]] ⊆ [[z.im, w.im]] →
        IntervalIntegrable (fun y : ℝ => f (x + y * I)) MeasureTheory.volume y₁ y₂ := by
      intro x hx y₁ y₂ hy
      refine ContinuousOn.intervalIntegrable ?_
      refine hc.comp (by fun_prop) fun y hy' => hzw ?_
      simp only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
        mul_zero, sub_zero, add_im, mul_im, mul_one, add_zero, zero_add]
      exact ⟨hx, hy hy'⟩
    rw [rectBdry_split f z w b (hvert _ right_mem_uIcc _ _ (uIcc_subset_uIcc_left hbI))
      (hvert _ right_mem_uIcc _ _ (uIcc_subset_uIcc_right hbI))
      (hvert _ left_mem_uIcc _ _ (uIcc_subset_uIcc_left hbI))
      (hvert _ left_mem_uIcc _ _ (uIcc_subset_uIcc_right hbI))]
    have e1 : rectBdry f z (w.re + b * I) = 0 := by
      refine key _ _ (fun x hx => hzw ?_) ?_
      · simp only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
          mul_zero, sub_zero, add_im, mul_im, mul_one, add_zero, zero_add] at hx ⊢
        exact ⟨hx.1, uIcc_subset_uIcc_left hbI hx.2⟩
      · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
          zero_add, add_zero]
        exact not_mem_Ioo_min_max _ _
    have e2 : rectBdry f (z.re + b * I) w = 0 := by
      refine key _ _ (fun x hx => hzw ?_) ?_
      · simp only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
          mul_zero, sub_zero, add_im, mul_im, mul_one, add_zero, zero_add] at hx ⊢
        exact ⟨hx.1, uIcc_subset_uIcc_right hbI hx.2⟩
      · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
          zero_add, add_zero]
        exact not_mem_Ioo_min_max' _ _
    rw [e1, e2, add_zero]
  · exact key z w hzw hb

/-- **Boundary uniqueness.** If `f` is holomorphic on a connected open set `U` containing the upper
half of a disc centred on the real axis, continuous on the closed upper half of the disc, and zero
on its diameter, then `f = 0` on `U`. -/
theorem eqOn_zero_of_boundary {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) {x₀ r : ℝ} (hr : 0 < r)
    (hsub : ball (x₀ : ℂ) r ∩ {z | 0 < z.im} ⊆ U)
    (hcont : ContinuousOn f (ball (x₀ : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hzero : ∀ z ∈ ball (x₀ : ℂ) r, z.im = 0 → f z = 0) : EqOn f 0 U := by
  classical
  set g : ℂ → ℂ := fun z => if 0 < z.im then f z else 0 with hg
  have hopenP : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hopenM : IsOpen {z : ℂ | z.im < 0} := isOpen_lt continuous_im continuous_const
  have hgP : ∀ z : ℂ, 0 < z.im → g =ᶠ[𝓝 z] f := fun z hz =>
    Filter.mem_of_superset (hopenP.mem_nhds hz) fun w hw => by simp [hg, show 0 < w.im from hw]
  have hgM : ∀ z : ℂ, z.im < 0 → g =ᶠ[𝓝 z] fun _ => (0 : ℂ) := fun z hz =>
    Filter.mem_of_superset (hopenM.mem_nhds hz) fun w hw => by
      simp [hg, not_lt.2 (le_of_lt (show w.im < 0 from hw))]
  have hfU : ∀ z ∈ ball (x₀ : ℂ) r, 0 < z.im → DifferentiableAt ℂ f z := fun z hz hz' =>
    hf.differentiableAt (hU.mem_nhds (hsub ⟨hz, hz'⟩))
  have hgc : ContinuousOn g (ball (x₀ : ℂ) r) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact continuous_const.continuousAt.congr (hgM z h).symm
    · have hz0 : g z = 0 := by simp [hg, h]
      have hfz : f z = 0 := hzero z hz h
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hcont z ⟨hz, h.ge⟩) ε hε
      obtain ⟨ρ, hρ, hρ'⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
      refine ⟨min δ ρ, lt_min hδ hρ, fun {x} hx => ?_⟩
      rw [hz0]
      by_cases hxi : 0 < x.im
      · have hgx : g x = f x := by simp [hg, hxi]
        rw [hgx]
        have := hδ' ⟨hρ' (lt_of_lt_of_le hx (min_le_right _ _)), hxi.le⟩
          (lt_of_lt_of_le hx (min_le_left _ _))
        rwa [hfz] at this
      · have hgx : g x = 0 := by simp [hg, hxi]
        rw [hgx, dist_self]; exact hε
    · exact (hfU z hz h).continuousAt.congr (hgP z h).symm
  have hgd : DifferentiableOn ℂ g (ball (x₀ : ℂ) r \ {z | z.im = 0}) := by
    rintro z ⟨hz, hz'⟩
    apply DifferentiableAt.differentiableWithinAt
    rcases lt_or_gt_of_ne (show z.im ≠ 0 from hz') with h | h
    · exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (hgM z h)
    · exact (hfU z hz h).congr_of_eventuallyEq (hgP z h)
  have hgA := (differentiableOn_ball_of_line hgc hgd).analyticOnNhd isOpen_ball
  have hnorm : ‖((r / 2 : ℝ) : ℂ) * I‖ = r / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set p : ℂ := (x₀ : ℂ) - ((r / 2 : ℝ) : ℂ) * I
  set q : ℂ := (x₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * I
  have hp : p ∈ ball (x₀ : ℂ) r := by
    rw [mem_ball, dist_eq_norm, show p - x₀ = -(((r / 2 : ℝ) : ℂ) * I) by simp [p], norm_neg,
      hnorm]
    linarith
  have hq : q ∈ ball (x₀ : ℂ) r := by
    rw [mem_ball, dist_eq_norm, show q - x₀ = ((r / 2 : ℝ) : ℂ) * I by simp [q], hnorm]
    linarith
  have hpim : p.im < 0 := by simp [p]; linarith
  have hqim : 0 < q.im := by simp [q]; linarith
  have hgz : EqOn g 0 (ball (x₀ : ℂ) r) :=
    hgA.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hp
      (hgM p hpim)
  have hfq : f =ᶠ[𝓝 q] 0 := by
    refine Filter.eventually_of_mem ((isOpen_ball.inter hopenP).mem_nhds ⟨hq, hqim⟩) ?_
    rintro w ⟨hw, hw'⟩
    have := hgz hw
    simp only [hg, show 0 < w.im from hw', ite_true, Pi.zero_apply] at this
    simpa using this
  exact (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc
    (hsub ⟨hq, hqim⟩) hfq

end ZetaF
