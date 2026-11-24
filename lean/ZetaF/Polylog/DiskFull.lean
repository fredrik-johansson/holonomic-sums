/-
# Theorem 4.1(1) on the whole punctured disc (minus `[0, 1)`)

For `z = e^{2πiα}` with `0 < Re α < 1` and `Im α > 0`, i.e. `0 < |z| < 1`, `z ∉ (0, 1)`, every
dual point `c_n = π²(n - α)²` lies in the slit plane `ℂ ∖ (-∞, 0]` (`geoDualC_mem_slitPlane`).
With the dual integrals continued there (`JslitE`, `JslitO` from `Polylog/Slit.lean`), the
right-hand side of the splitting (`polylogRHSS`, with `H` and `L_k` their termwise series) is
holomorphic in `α` on the strip `0 < Re α < 1` (`differentiableOn_polylogRHSS`); for all but finitely
many `n` near a given `α`, `Re c_n` is large and the bounds of `DiskEntire` apply.  It agrees with
`polylogRHSE` on the diamond (`polylogRHSS_eq_polylogRHSE`).  The left-hand side is holomorphic in `α`
for `Im α > 0` and every `s` (`differentiableOn_lhs_all`).  Both sides agree on the upper diamond
(`polylogTail_split_disk_all`), so by the identity theorem on the (convex) half-strip they agree on
all of it, for every `s ∈ ℂ` (`polylogTail_split_halfStrip`).

The boundary case `0 < z < 1` (`α = iy`) is `polylogTail_split_boundary`: there `c₀ = -π²y²` is on
the cut and `J^{(δ)}(c₀)` is the boundary value from `Im c > 0` (`JupE`, `JupO`), as in the paper.
-/
import ZetaF.Polylog.Slit

open MeasureTheory Set Filter Metric
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-! ### The strip and the dual points -/

/-- The strip `0 < Re α < 1`. -/
def strip : Set ℂ := {α | 0 < α.re ∧ α.re < 1}

/-- The half-strip `0 < Re α < 1`, `Im α > 0`: `z = e^{2πiα}` runs over `{0 < |z| < 1} ∖ (0, 1)`. -/
def halfStrip : Set ℂ := {α | 0 < α.re ∧ α.re < 1 ∧ 0 < α.im}

lemma isOpen_strip : IsOpen strip := by
  have e : strip = {α : ℂ | 0 < α.re} ∩ {α : ℂ | α.re < 1} := rfl
  rw [e]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma isOpen_halfStrip : IsOpen halfStrip := by
  have e : halfStrip = {α : ℂ | 0 < α.re} ∩ ({α : ℂ | α.re < 1} ∩ {α : ℂ | 0 < α.im}) := rfl
  rw [e]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

lemma convex_halfStrip : Convex ℝ halfStrip := by
  have e : halfStrip = {α : ℂ | 0 < α.re} ∩ ({α : ℂ | α.re < 1} ∩ {α : ℂ | 0 < α.im}) := rfl
  rw [e]
  exact (convex_halfSpace_re_gt 0).inter ((convex_halfSpace_re_lt 1).inter
    (convex_halfSpace_im_gt 0))

lemma halfStrip_subset_strip : halfStrip ⊆ strip := fun _ h => ⟨h.1, h.2.1⟩

lemma upperDiamond_subset_halfStrip : upperDiamond ⊆ halfStrip := by
  rintro α ⟨h1, h2, h3⟩
  exact ⟨by linarith, by linarith, h1⟩

lemma geoDualC_im (α : ℂ) (n : ℤ) :
    (geoDualC α n).im = -(2 * π ^ 2 * ((n : ℝ) - α.re) * α.im) := by
  simp only [geoDualC, pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
  ring

/-- `c_n = π²(n - α)²` lies in the slit plane unless `Re α = n`. -/
lemma geoDualC_mem_slitPlane_of_ne {α : ℂ} {n : ℤ} (hne : (n : ℝ) - α.re ≠ 0) :
    geoDualC α n ∈ Complex.slitPlane := by
  rcases eq_or_ne α.im 0 with h | h
  · left
    rw [geoDualC_re, h]
    have : 0 < ((n : ℝ) - α.re) ^ 2 := by positivity
    have hπ : 0 < π ^ 2 := by positivity
    nlinarith
  · right
    rw [geoDualC_im]
    have : (2 * π ^ 2 : ℝ) ≠ 0 := by positivity
    exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero this hne) h)

/-- For `0 < Re α < 1` every dual point `c_n` lies in the slit plane. -/
lemma geoDualC_mem_slitPlane {α : ℂ} (hα : α ∈ strip) (n : ℤ) :
    geoDualC α n ∈ Complex.slitPlane := by
  refine geoDualC_mem_slitPlane_of_ne ?_
  have hd := min_le_abs_int_sub hα.1 hα.2 n
  have : 0 < min α.re (1 - α.re) := lt_min hα.1 (by linarith [hα.2])
  intro h; rw [h, abs_zero] at hd; linarith

/-- `Re c_n ≥ π²(|n| - 1)` once `|n| - 1 ≥ |Im α| + 1`. -/
lemma geoDualC_re_ge_lin {α : ℂ} (hα : |α.re| ≤ 1) {Y : ℝ} (hY : |α.im| ≤ Y) {n : ℤ}
    (hn : Y + 2 ≤ |(n : ℝ)|) : π ^ 2 * (|(n : ℝ)| - 1) ≤ (geoDualC α n).re := by
  rw [geoDualC_re]
  have h1 : |(n : ℝ)| - 1 ≤ |(n : ℝ) - α.re| := by
    have := abs_sub_abs_le_abs_sub (n : ℝ) α.re
    linarith
  set d := |(n : ℝ)| - 1
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans hY
  have hd : Y + 1 ≤ d := by simp only [d]; linarith
  have hsq : d ^ 2 ≤ ((n : ℝ) - α.re) ^ 2 := by
    rw [← sq_abs ((n : ℝ) - α.re)]
    exact pow_le_pow_left₀ (by linarith) h1 2
  have him : α.im ^ 2 ≤ Y ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hY 2
  have : d ≤ d ^ 2 - Y ^ 2 := by nlinarith
  have hπ : 0 < π ^ 2 := by positivity
  nlinarith

/-! ### The dual terms with continued `J` -/

/-- The dual term `J^{(0)}_s(c_n) - iπ(n - α) J^{(1)}_{s+1}(c_n)` with `J` continued to the slit
plane. -/
noncomputable def dualTermS (a : ℕ → ℂ) (u₀ : ℝ) (s α : ℂ) (n : ℤ) : ℂ :=
  JslitE a u₀ s (geoDualC α n) - Complex.I * π * ((n : ℂ) - α) * JslitO a u₀ s (geoDualC α n)

section DualS

variable (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) (s : ℂ)
include ha hR hu₀

lemma dualTermS_eq {α : ℂ} {n : ℤ} (hre : 0 < (geoDualC α n).re) :
    dualTermS a u₀ s α n = dualTermC a u₀ s α n := by
  unfold dualTermS dualTermC
  rw [JslitE_eq ha hR hu₀ hre, JslitO_eq ha hR hu₀ hre]

lemma differentiableAt_dualTermS_of_mem {α : ℂ} {n : ℤ}
    (hc : geoDualC α n ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun α => dualTermS a u₀ s α n) α := by
  have hd : Differentiable ℂ fun α => geoDualC α n := fun α =>
    (differentiableAt_const _).mul (((differentiableAt_const _).sub differentiableAt_id).pow 2)
  have hmem := Complex.isOpen_slitPlane.mem_nhds hc
  have hE := (differentiableOn_JslitE ha hR hu₀ s).differentiableAt hmem
  have hO := (differentiableOn_JslitO ha hR hu₀ s).differentiableAt hmem
  have hlin : DifferentiableAt ℂ (fun α : ℂ => Complex.I * π * ((n : ℂ) - α)) α :=
    (differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)
  have h0 : DifferentiableAt ℂ (fun α => JslitE a u₀ s (geoDualC α n)) α :=
    DifferentiableAt.fun_comp' (f := fun α => geoDualC α n) (g := JslitE a u₀ s) α hE (hd α)
  have h1 : DifferentiableAt ℂ (fun α => JslitO a u₀ s (geoDualC α n)) α :=
    DifferentiableAt.fun_comp' (f := fun α => geoDualC α n) (g := JslitO a u₀ s) α hO (hd α)
  unfold dualTermS
  exact h0.sub (hlin.mul h1)

lemma differentiableAt_dualTermS {α : ℂ} (hα : α ∈ strip) (n : ℤ) :
    DifferentiableAt ℂ (fun α => dualTermS a u₀ s α n) α :=
  differentiableAt_dualTermS_of_mem ha hR hu₀ s (geoDualC_mem_slitPlane hα n)

/-- A dual sum over `ℤ` is holomorphic on an open set `U ⊆ {|Re α| ≤ 1}` if its terms are, and
they are the dual terms `dualTermC` (with convergent integrals) wherever `Re c_n ≥ 1`. -/
theorem differentiableOn_dualSum_gen {f : ℂ → ℤ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUre : ∀ α ∈ U, |α.re| ≤ 1) (hf : ∀ n, ∀ α ∈ U, DifferentiableAt ℂ (fun α => f α n) α)
    (heq : ∀ n α, α ∈ U → 1 ≤ (geoDualC α n).re → f α n = dualTermC a u₀ s α n) :
    DifferentiableOn ℂ (fun α => ∑' n : ℤ, f α n) U := by
  intro α₀ hα₀
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 hU α₀ hα₀
  set ρ := min (ε / 2) 1
  have hρ : 0 < ρ := lt_min (by linarith) one_pos
  have hcl : closedBall α₀ ρ ⊆ U :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hεs
  have hball : ball α₀ ρ ⊆ U := ball_subset_closedBall.trans hcl
  set Y := |α₀.im| + 1
  have hY : ∀ α ∈ ball α₀ ρ, |α.im| ≤ Y := fun α hα => by
    rw [mem_ball, dist_eq_norm] at hα
    have h1 := Complex.abs_im_le_norm (α - α₀)
    rw [Complex.sub_im] at h1
    have := abs_sub_abs_le_abs_sub α.im α₀.im
    have : ρ ≤ 1 := min_le_right _ _
    simp only [Y]; linarith
  -- bounds for the dual integrals with `Re c ≥ 1`
  obtain ⟨B₀, hB₀⟩ := dualJC_local_bound ha hR hu₀ one_pos s (a := a)
  obtain ⟨B₁, hB₁⟩ := dualJOddC_local_bound ha hR hu₀ one_pos s (a := a)
  have hB₀0 : 0 ≤ B₀ := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1
    ((norm_nonneg _).trans (hB₀ s (mem_ball_self one_pos) 1 (by simp)))
  have hB₁0 : 0 ≤ B₁ := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1
    ((norm_nonneg _).trans (hB₁ s (mem_ball_self one_pos) 1 (by simp)))
  set l := π ^ 2 / u₀
  have hl : 0 < l := by positivity
  set A := B₀ + π * (1 + Y) * B₁
  set B := π * B₁
  set g : ℤ → ℝ := fun n => rexp (1 / u₀) * (rexp (-(l * (|(n : ℝ)| - 1))) * (A + B * |(n : ℝ)|))
  have hg : Summable g := (summable_int_exp_abs hl A B).mul_left _
  have hfar : ∀ n : ℤ, Y + 2 ≤ |(n : ℝ)| → ∀ α ∈ ball α₀ ρ, ‖f α n‖ ≤ g n := by
    intro n hn α hα
    have hre1 := hUre α (hball hα)
    have hlin := geoDualC_re_ge_lin hre1 (hY α hα) hn
    have hn1 : 1 ≤ |(n : ℝ)| - 1 := by have := (abs_nonneg α₀.im); simp only [Y] at hn; linarith
    have hπ : 1 ≤ π ^ 2 := by nlinarith [Real.two_le_pi]
    have hc1 : 1 ≤ (geoDualC α n).re := by nlinarith
    rw [heq n α (hball hα) hc1]
    set E := rexp (-(((geoDualC α n).re - 1) / u₀))
    have hE : E ≤ rexp (1 / u₀) * rexp (-(l * (|(n : ℝ)| - 1))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : l * (|(n : ℝ)| - 1) = π ^ 2 * (|(n : ℝ)| - 1) / u₀ := by simp only [l]; ring
      rw [this, sub_div]
      have := div_le_div_of_nonneg_right hlin hu₀.le
      linarith
    have hnα : ‖(n : ℂ) - α‖ ≤ |(n : ℝ)| + (1 + Y) := by
      calc ‖(n : ℂ) - α‖ ≤ ‖(n : ℂ)‖ + ‖α‖ := norm_sub_le _ _
        _ ≤ |(n : ℝ)| + (|α.re| + |α.im|) := by
            gcongr
            · rw [Complex.norm_intCast]
            · exact Complex.norm_le_abs_re_add_abs_im α
        _ ≤ |(n : ℝ)| + (1 + Y) := by
            linarith [hre1, hY α hα]
    have hJ0 := hB₀ s (mem_ball_self one_pos) _ hc1
    have hJ1 := hB₁ s (mem_ball_self one_pos) _ hc1
    unfold dualTermC
    have hY0 : 0 ≤ Y := by positivity
    calc _ ≤ ‖geoJC (kernel a s) u₀ (1 / 2) (geoDualC α n)‖ +
          ‖Complex.I * π * ((n : ℂ) - α)‖ *
            ‖geoJC (kernel a (s + 1)) u₀ (3 / 2) (geoDualC α n)‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      _ ≤ E * B₀ + (π * (|(n : ℝ)| + (1 + Y))) * (E * B₁) := by
          gcongr
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_of_nonneg Real.pi_pos.le]
          exact mul_le_mul_of_nonneg_left hnα Real.pi_pos.le
      _ = E * (A + B * |(n : ℝ)|) := by simp only [A, B]; ring
      _ ≤ (rexp (1 / u₀) * rexp (-(l * (|(n : ℝ)| - 1)))) * (A + B * |(n : ℝ)|) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
      _ = g n := by simp only [g]; ring
  -- the finitely many remaining terms are bounded by compactness
  have hfin : ∀ n : ℤ, ∃ G, ∀ α ∈ closedBall α₀ ρ, ‖f α n‖ ≤ G := fun n =>
    (isCompact_closedBall α₀ ρ).exists_bound_of_continuousOn
      (fun α hα => (hf n α (hcl hα)).continuousAt.continuousWithinAt)
  choose G hG using hfin
  set N : ℕ := ⌈Y + 2⌉₊
  set u : ℤ → ℝ := fun n => if |(n : ℝ)| < N then G n else g n
  have hu : Summable u := by
    have h1 : Summable fun n : ℤ => if |(n : ℝ)| < N then G n - g n else 0 := by
      refine summable_of_ne_finset_zero (s := Finset.Ioo (-(N : ℤ)) N) fun n hn => ?_
      have : ¬ |(n : ℝ)| < N := by
        intro h
        apply hn
        rw [abs_lt] at h
        simp only [Finset.mem_Ioo]
        constructor <;> [exact_mod_cast h.1; exact_mod_cast h.2]
      simp [this]
    refine (hg.add h1).congr fun n => ?_
    simp only [u]; split_ifs <;> ring
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n => fun α hα => (hf n α (hball hα)).differentiableWithinAt)
    isOpen_ball (fun n α hα => by
      simp only [u]
      split_ifs with h
      · exact hG n α (ball_subset_closedBall hα)
      · refine hfar n ?_ α hα
        exact (Nat.le_ceil _).trans (not_lt.1 h))
  exact (hd.differentiableAt (ball_mem_nhds α₀ hρ)).differentiableWithinAt

/-- **The dual sum is holomorphic in `α` on the strip `0 < Re α < 1`.** -/
theorem differentiableOn_dualSumS :
    DifferentiableOn ℂ (fun α => ∑' n : ℤ, dualTermS a u₀ s α n) strip :=
  differentiableOn_dualSum_gen ha hR hu₀ s isOpen_strip
    (fun α hα => abs_le.2 ⟨by linarith [hα.1], hα.2.le⟩)
    (fun n α hα => differentiableAt_dualTermS ha hR hu₀ s hα n)
    (fun n α _ h => dualTermS_eq ha hR hu₀ s (by linarith))

end DualS

/-! ### The right-hand side on the strip -/

/-- **The right-hand side of Theorem 4.1(1) on the whole disc**: as `polylogRHSE`, with the dual
integrals continued to the slit plane. -/
noncomputable def polylogRHSS (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (α s : ℂ) : ℂ :=
  (∑' k, kSumTermC a k₀ u₀ s k α) + ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, dualTermS a u₀ s α n -
    1 / 2 * (∑' n, hSeriesTerm a u₀ n s) -
    ∑ k ∈ Finset.Ico 1 k₀, (geoC (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n s) +
      (k : ℂ) * geoS (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n (s + 1)))

/-- The right-hand side is holomorphic in `α` on the strip `0 < Re α < 1`, for every `s`. -/
theorem differentiableOn_polylogRHSS (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ}
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) (s : ℂ) :
    DifferentiableOn ℂ (fun α => polylogRHSS a k₀ u₀ α s) strip := by
  have hfin : Differentiable ℂ fun α => ∑ k ∈ Finset.Ico 1 k₀,
      (geoC (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n s) +
        (k : ℂ) * geoS (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n (s + 1))) :=
    Differentiable.fun_sum fun k _ => ((differentiable_geoC k).mul_const _).add
      (((differentiable_geoS k).const_mul _).mul_const _)
  unfold polylogRHSS
  exact ((((differentiable_kSumC ha hR hRk hu₀ s).differentiableOn).add
    ((differentiableOn_dualSumS ha hR hu₀ s).const_mul _)).sub_const _).sub hfin.differentiableOn

/-- On the diamond (where all `Re c_n > 0`) the continued right-hand side is `polylogRHSE`. -/
theorem polylogRHSS_eq_polylogRHSE (ha : GeomBounded a R) (hR : 0 ≤ R) (k₀ : ℕ) {u₀ : ℝ}
    (hu₀ : 0 < u₀) {α : ℂ} (hα : α ∈ diamond) (s : ℂ) :
    polylogRHSS a k₀ u₀ α s = polylogRHSE a k₀ u₀ α s := by
  unfold polylogRHSS polylogRHSE
  congr 4
  exact tsum_congr fun n => dualTermS_eq ha hR hu₀ s (geoDualC_re_pos hα n)

/-! ### The left-hand side -/

lemma norm_term_tail_le (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ} (hRk : R < k₀)
    (hF : ∀ k ≥ k₀, F k = evalInv a k) (s : ℂ) :
    ∃ M, 0 ≤ M ∧ ∀ n : ℕ, ‖LSeries.term (tail k₀ F) s n‖ ≤ M * (n : ℝ) ^ ⌈|s.re|⌉₊ := by
  obtain ⟨M, hM⟩ := evalInv_bounded hR ha hRk
  refine ⟨max M 0, le_max_right _ _, fun n => ?_⟩
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have htail : ‖tail k₀ F n‖ ≤ max M 0 := by
    unfold tail
    split_ifs with hk
    · rw [hF n hk]
      have := hM n (by exact_mod_cast hk)
      exact this.trans (le_max_left _ _)
    · simp
  have hre : -s.re ≤ (⌈|s.re|⌉₊ : ℝ) := (neg_le_abs _).trans (Nat.le_ceil _)
  rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith), ← Real.rpow_natCast]
  exact mul_le_mul htail (Real.rpow_le_rpow_of_exponent_le hn1 hre)
    (Real.rpow_nonneg (by linarith) _) (le_max_right _ _)

/-- `Li_F^{≥k₀}(s, e^{2πiα})` is holomorphic in `α` for `Im α > 0`, for every `s`. -/
theorem differentiableOn_lhs_all (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) (s : ℂ) :
    DifferentiableOn ℂ (fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) {α | 0 < α.im} := by
  intro α₀ hα₀
  have hα₀ : 0 < α₀.im := hα₀
  obtain ⟨M, hM0, hM⟩ := norm_term_tail_le ha hR hRk hF s
  set δ := α₀.im / 2
  have hδ : 0 < δ := by positivity
  set r := rexp (-(2 * π * δ))
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff, neg_lt_zero]; positivity
  simp only [lhs_eq]
  have hd := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun n α => LSeries.term (tail k₀ F) s n * geoZ α ^ n)
    ((summable_pow_mul_geometric_of_norm_lt_one ⌈|s.re|⌉₊ hr).mul_left M)
    (fun n => ((differentiable_geoZ.pow n).const_mul _).differentiableOn) (isOpen_ball (x := α₀) (ε := δ))
    (fun n α hα => by
      rw [mem_ball, dist_eq_norm] at hα
      have him : δ ≤ α.im := by
        have h1 := Complex.abs_im_le_norm (α - α₀)
        rw [Complex.sub_im] at h1
        simp only [δ] at hα ⊢
        linarith [neg_abs_le (α.im - α₀.im)]
      rw [norm_mul, norm_pow, norm_geoZ]
      have hz : rexp (-(2 * π * α.im)) ≤ r := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
      calc ‖LSeries.term (tail k₀ F) s n‖ * rexp (-(2 * π * α.im)) ^ n
          ≤ (M * (n : ℝ) ^ ⌈|s.re|⌉₊) * r ^ n :=
            mul_le_mul (hM n) (pow_le_pow_left₀ (Real.exp_pos _).le hz n) (by positivity)
              (by positivity)
        _ = M * ((n : ℝ) ^ ⌈|s.re|⌉₊ * r ^ n) := by ring)
  exact (hd.differentiableAt (ball_mem_nhds α₀ hδ)).differentiableWithinAt

/-! ### Theorem 4.1(1) on the disc -/

/-- **Theorem 4.1(1) for `0 < |z| < 1`, `z ∉ (0, 1)`, and all `s`**: for `z = e^{2πiα}` with
`0 < Re α < 1`, `Im α > 0`, `Li_F^{≥k₀}(s, z)` equals the splitting with dual points
`c_n = π²(n - α)²` in the slit plane, the dual integrals `J^{(δ)}(c_n)` continued there (`JslitE`,
`JslitO`), and `H`, `L_k` given by their termwise series. -/
theorem polylogTail_split_halfStrip (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {α : ℂ} (hα : α ∈ halfStrip) (s : ℂ) :
    zetaTail (fun k => F k * geoZ α ^ k) k₀ s = polylogRHSS a k₀ u₀ α s := by
  set α₀ : ℂ := ⟨1 / 2, 1 / 4⟩
  have hα₀ : α₀ ∈ upperDiamond := ⟨by norm_num [α₀], by norm_num [α₀], by norm_num [α₀]⟩
  have hL : AnalyticOnNhd ℂ (fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) halfStrip :=
    ((differentiableOn_lhs_all ha hR hRk hF s).mono fun α (h : α ∈ halfStrip) => h.2.2).analyticOnNhd
      isOpen_halfStrip
  have hRHS : AnalyticOnNhd ℂ (fun α => polylogRHSS a k₀ u₀ α s) halfStrip :=
    ((differentiableOn_polylogRHSS ha hR hRk hu₀ s).mono halfStrip_subset_strip).analyticOnNhd
      isOpen_halfStrip
  have hev : (fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) =ᶠ[𝓝 α₀]
      fun α => polylogRHSS a k₀ u₀ α s := by
    filter_upwards [isOpen_upperDiamond.mem_nhds hα₀] with β hβ
    have hβd := (upperDiamond_subset hβ).2
    rw [polylogRHSS_eq_polylogRHSE ha hR k₀ hu₀ hβd]
    exact polylogTail_split_disk_all ha hR hk₀ hRk hF hu₀ hβ.1 hβd s
  exact hL.eqOn_of_preconnected_of_eventuallyEq hRHS convex_halfStrip.isPreconnected
    (upperDiamond_subset_halfStrip hα₀) hev hα

/-! ### The boundary case `0 < z < 1`

For `α = iy`, `y > 0` (`z = e^{-2πy} ∈ (0, 1)`), the dual point `c₀ = -π²y²` lies on the cut.
There `J^{(δ)}(c₀)` denotes the boundary value from `Im c > 0` (`JupE`, `JupO`; see
`tendsto_JslitE_JupE`).  Near `iy` the right-hand side with this boundary value at `n = 0`
(`polylogRHSB`) is holomorphic in `α`, and it agrees with `polylogRHSS` for `Re α > 0` (where
`Im c₀ = 2π² Re α Im α > 0`); the identity theorem on a ball around `iy` gives the identity at `iy`.
-/

/-- The dual term with the boundary value `J⁺` at `n = 0`. -/
noncomputable def dualTermB (a : ℕ → ℂ) (u₀ : ℝ) (s α : ℂ) (n : ℤ) : ℂ :=
  if n = 0 then
    JupE a u₀ s (geoDualC α n) - Complex.I * π * ((n : ℂ) - α) * JupO a u₀ s (geoDualC α n)
  else dualTermS a u₀ s α n

/-- The right-hand side for `0 < z < 1`: as `polylogRHSS`, with `J⁺(c₀)` at `n = 0`. -/
noncomputable def polylogRHSB (a : ℕ → ℂ) (k₀ : ℕ) (u₀ : ℝ) (α s : ℂ) : ℂ :=
  (∑' k, kSumTermC a k₀ u₀ s k α) + ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, dualTermB a u₀ s α n -
    1 / 2 * (∑' n, hSeriesTerm a u₀ n s) -
    ∑ k ∈ Finset.Ico 1 k₀, (geoC (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n s) +
      (k : ℂ) * geoS (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n (s + 1)))

/-- The ball around `iy` on which we work. -/
noncomputable def bdryBall (y : ℝ) : Set ℂ := ball ((y : ℂ) * Complex.I) (min (1 / 4) (y / 8))

lemma bdryBall_props {y : ℝ} (_hy : 0 < y) {α : ℂ} (hα : α ∈ bdryBall y) :
    |α.re| < 1 / 4 ∧ |α.re| < y / 8 ∧ 7 * y / 8 < α.im := by
  unfold bdryBall at hα
  rw [mem_ball, dist_eq_norm] at hα
  have h1 := Complex.abs_re_le_norm (α - (y : ℂ) * Complex.I)
  have h2 := Complex.abs_im_le_norm (α - (y : ℂ) * Complex.I)
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero] at h1 h2
  have hm1 : min (1 / 4) (y / 8) ≤ 1 / 4 := min_le_left _ _
  have hm2 : min (1 / 4) (y / 8) ≤ y / 8 := min_le_right _ _
  refine ⟨by linarith, by linarith, ?_⟩
  have := neg_abs_le (α.im - y)
  linarith

lemma geoDualC_zero_mem_upPlane {y : ℝ} (hy : 0 < y) {α : ℂ} (hα : α ∈ bdryBall y) :
    geoDualC α 0 ∈ upPlane := by
  obtain ⟨-, h2, h3⟩ := bdryBall_props hy hα
  show 0 < (geoDualC α 0 * pUp).re
  rw [re_mul_pUp, geoDualC_re, geoDualC_im]
  rw [abs_lt] at h2
  push_cast
  have hπ : 0 < π ^ 2 := by positivity
  have hk : 0 < α.im ^ 2 + 2 * α.re * α.im - α.re ^ 2 := by nlinarith
  nlinarith

lemma geoDualC_zero_re_neg {y : ℝ} (hy : 0 < y) {α : ℂ} (hα : α ∈ bdryBall y) :
    (geoDualC α 0).re < 0 := by
  obtain ⟨-, h2, h3⟩ := bdryBall_props hy hα
  rw [geoDualC_re]
  rw [abs_lt] at h2
  push_cast
  have hπ : 0 < π ^ 2 := by positivity
  have : (0 - α.re) ^ 2 - α.im ^ 2 < 0 := by nlinarith
  nlinarith

lemma geoDualC_ne_zero_mem_slitPlane {y : ℝ} (hy : 0 < y) {α : ℂ} (hα : α ∈ bdryBall y)
    {n : ℤ} (hn : n ≠ 0) : geoDualC α n ∈ Complex.slitPlane := by
  obtain ⟨h1, -, -⟩ := bdryBall_props hy hα
  refine geoDualC_mem_slitPlane_of_ne ?_
  have : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  intro h
  have : |(n : ℝ)| = |α.re| := by rw [show (n : ℝ) = α.re by linarith]
  linarith

section Boundary

variable (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) (s : ℂ) {y : ℝ} (hy : 0 < y)
include ha hR hu₀ hy

lemma differentiableAt_dualTermB {α : ℂ} (hα : α ∈ bdryBall y) (n : ℤ) :
    DifferentiableAt ℂ (fun α => dualTermB a u₀ s α n) α := by
  by_cases hn : n = 0
  · subst hn
    simp only [dualTermB, ite_true]
    have hd : Differentiable ℂ fun α => geoDualC α (0 : ℤ) := fun α =>
      (differentiableAt_const _).mul (((differentiableAt_const _).sub differentiableAt_id).pow 2)
    have hmem := isOpen_upPlane.mem_nhds (geoDualC_zero_mem_upPlane hy hα)
    have hE := (differentiableOn_JupE ha hR hu₀ s).differentiableAt hmem
    have hO := (differentiableOn_JupO ha hR hu₀ s).differentiableAt hmem
    have hlin : DifferentiableAt ℂ (fun α : ℂ => Complex.I * π * (((0 : ℤ) : ℂ) - α)) α :=
      (differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)
    have h0 : DifferentiableAt ℂ (fun α => JupE a u₀ s (geoDualC α (0 : ℤ))) α :=
      DifferentiableAt.fun_comp' (f := fun α => geoDualC α (0 : ℤ)) (g := JupE a u₀ s) α hE (hd α)
    have h1 : DifferentiableAt ℂ (fun α => JupO a u₀ s (geoDualC α (0 : ℤ))) α :=
      DifferentiableAt.fun_comp' (f := fun α => geoDualC α (0 : ℤ)) (g := JupO a u₀ s) α hO (hd α)
    exact h0.sub (hlin.mul h1)
  · have e : (fun α => dualTermB a u₀ s α n) = fun α => dualTermS a u₀ s α n := by
      funext α; simp [dualTermB, hn]
    rw [e]
    exact differentiableAt_dualTermS_of_mem ha hR hu₀ s (geoDualC_ne_zero_mem_slitPlane hy hα hn)

theorem differentiableOn_polylogRHSB {k₀ : ℕ} (hRk : R < k₀) :
    DifferentiableOn ℂ (fun α => polylogRHSB a k₀ u₀ α s) (bdryBall y) := by
  have hdual : DifferentiableOn ℂ (fun α => ∑' n : ℤ, dualTermB a u₀ s α n) (bdryBall y) :=
    differentiableOn_dualSum_gen ha hR hu₀ s isOpen_ball
      (fun α hα => (bdryBall_props hy hα).1.le.trans (by norm_num))
      (fun n α hα => differentiableAt_dualTermB ha hR hu₀ s hy hα n)
      (fun n α hα h => by
        by_cases hn : n = 0
        · subst hn; linarith [geoDualC_zero_re_neg hy hα]
        · simp only [dualTermB, hn, ite_false]
          exact dualTermS_eq ha hR hu₀ s (by linarith))
  have hfin : Differentiable ℂ fun α => ∑ k ∈ Finset.Ico 1 k₀,
      (geoC (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n s) +
        (k : ℂ) * geoS (geoZ α) k * (∑' n, lSeriesTerm a u₀ k n (s + 1))) :=
    Differentiable.fun_sum fun k _ => ((differentiable_geoC k).mul_const _).add
      (((differentiable_geoS k).const_mul _).mul_const _)
  unfold polylogRHSB
  exact ((((differentiable_kSumC ha hR hRk hu₀ s).differentiableOn).add
    (hdual.const_mul _)).sub_const _).sub hfin.differentiableOn

omit ha hR in
lemma polylogRHSB_eq_polylogRHSS (k₀ : ℕ) {α : ℂ} (hα : α ∈ bdryBall y) (hre : 0 < α.re) :
    polylogRHSB a k₀ u₀ α s = polylogRHSS a k₀ u₀ α s := by
  unfold polylogRHSB polylogRHSS
  congr 4
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    have him : 0 < (geoDualC α (0 : ℤ)).im := by
      rw [geoDualC_im]
      have := (bdryBall_props hy hα).2.2
      push_cast
      have : 0 < 2 * π ^ 2 * α.re * α.im :=
        mul_pos (mul_pos (by positivity) hre) (by linarith)
      linarith
    have hup := geoDualC_zero_mem_upPlane hy hα
    simp only [dualTermB, dualTermS, ite_true]
    rw [JslitE_eq_JupE hu₀ him hup, JslitO_eq_JupO hu₀ him hup]
  · simp [dualTermB, hn]

end Boundary

/-- **Theorem 4.1(1) for `0 < z < 1`** (`z = e^{-2πy}`, `α = iy`), every `s`: the dual point
`c₀ = -π²y²` lies on the cut, and `J^{(δ)}(c₀)` is the boundary value from `Im c > 0`
(`JupE`, `JupO`). -/
theorem polylogTail_split_boundary (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {u₀ : ℝ} (hu₀ : 0 < u₀)
    {y : ℝ} (hy : 0 < y) (s : ℂ) :
    zetaTail (fun k => F k * geoZ ((y : ℂ) * Complex.I) ^ k) k₀ s =
      polylogRHSB a k₀ u₀ ((y : ℂ) * Complex.I) s := by
  set β : ℂ := (y : ℂ) * Complex.I
  set ρ := min (1 / 4) (y / 8)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hβ : β ∈ bdryBall y := mem_ball_self hρ
  set β' : ℂ := β + ((ρ / 2 : ℝ) : ℂ)
  have hβ' : β' ∈ bdryBall y := by
    unfold bdryBall
    rw [mem_ball, dist_eq_norm, show β' - (y : ℂ) * Complex.I = ((ρ / 2 : ℝ) : ℂ) by
      simp only [β', β]; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hβ're : 0 < β'.re := by simp [β', β]; positivity
  have hsub : ∀ α ∈ bdryBall y, 0 < α.im := fun α hα => by
    linarith [(bdryBall_props hy hα).2.2]
  have hL : AnalyticOnNhd ℂ (fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) (bdryBall y) :=
    ((differentiableOn_lhs_all ha hR hRk hF s).mono hsub).analyticOnNhd isOpen_ball
  have hRHS : AnalyticOnNhd ℂ (fun α => polylogRHSB a k₀ u₀ α s) (bdryBall y) :=
    (differentiableOn_polylogRHSB ha hR hu₀ s hy hRk).analyticOnNhd isOpen_ball
  have hopen : IsOpen (bdryBall y ∩ {α : ℂ | 0 < α.re}) :=
    isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hev : (fun α => zetaTail (fun k => F k * geoZ α ^ k) k₀ s) =ᶠ[𝓝 β']
      fun α => polylogRHSB a k₀ u₀ α s := by
    filter_upwards [hopen.mem_nhds ⟨hβ', hβ're⟩] with α hα
    rw [polylogRHSB_eq_polylogRHSS hu₀ s hy k₀ hα.1 hα.2]
    have h1 := bdryBall_props hy hα.1
    refine polylogTail_split_halfStrip ha hR hk₀ hRk hF hu₀ ⟨hα.2, ?_, hsub α hα.1⟩ s
    linarith [le_abs_self α.re, h1.1]
  exact hL.eqOn_of_preconnected_of_eventuallyEq hRHS (convex_ball _ _).isPreconnected hβ' hev hβ

end ZetaF
