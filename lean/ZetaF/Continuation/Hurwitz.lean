/-
# Proposition 5.7: `ζ_F^{≥k₀}(s) = ∑_n a_n ζ(s+n, k₀)`

With `ζ(w, k₀) = ∑_{k ≥ k₀} k^{-w}` (continued by `ζ(w) - ∑_{k<k₀} k^{-w}` using Mathlib's
`riemannZeta`), we prove for `F(k) = f(1/k)`, `k ≥ k₀ > R`:
* the identity for `Re s > 1` (`zetaTail_eq_tsum_hurwitz`);
* that the right-hand side is holomorphic on `ℂ ∖ {1, 0, -1, …}` (`differentiableOn_hurwitzSeries`);
* that it has a simple pole at `1 - n` with residue `a_n` (`hurwitzSeries_residue`);
* that it agrees there with the continuation of Theorem 3.2 (`hurwitzSeries_eq_splitRHS`).
-/
import ZetaF.Continuation.Theorem
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex

open Complex Filter Topology Finset

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-- `ζ(w, k₀) = ζ(w) - ∑_{1 ≤ k < k₀} k^{-w}`. -/
noncomputable def hurwitzTail (k₀ : ℕ) (w : ℂ) : ℂ :=
  riemannZeta w - ∑ k ∈ Ico 1 k₀, (k : ℂ) ^ (-w)

lemma hurwitzTail_eq_tsum {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {w : ℂ} (hw : 1 < w.re) :
    hurwitzTail k₀ w = ∑' k : ℕ, ((k + k₀ : ℕ) : ℂ) ^ (-w) := by
  have hs : Summable fun n : ℕ => 1 / (n : ℂ) ^ w := Complex.summable_one_div_nat_cpow.2 hw
  have h := (hs.sum_add_tsum_nat_add k₀).symm
  rw [hurwitzTail, zeta_eq_tsum_one_div_nat_cpow hw, h]
  have hw0 : w ≠ 0 := Complex.ne_zero_of_one_lt_re hw
  have hfin : ∑ i ∈ range k₀, 1 / (i : ℂ) ^ w = ∑ k ∈ Ico 1 k₀, (k : ℂ) ^ (-w) := by
    rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hk₀]
    simp [zero_cpow hw0, Complex.cpow_neg]
  rw [hfin, add_sub_cancel_left]
  congr 1; funext k; rw [Complex.cpow_neg, one_div]

lemma differentiableAt_hurwitzTail (k₀ : ℕ) {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ (hurwitzTail k₀) w := by
  refine (differentiableAt_riemannZeta hw).sub ?_
  refine DifferentiableAt.fun_sum fun k hk => ?_
  have hk0 : (k : ℂ) ≠ 0 := by
    simp only [mem_Ico] at hk; exact_mod_cast (by omega : k ≠ 0)
  exact (differentiableAt_neg_iff.2 differentiableAt_id).const_cpow (Or.inl hk0)

/-- `|ζ(w, k₀)| ≤ k₀^{2 - Re w} ∑_{k ≥ k₀} k^{-2}` for `Re w ≥ 2`. -/
lemma norm_hurwitzTail_le {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {w : ℂ} (hw : 2 ≤ w.re) :
    ‖hurwitzTail k₀ w‖ ≤ (k₀ : ℝ) ^ (2 - w.re) * ∑' k : ℕ, (((k + k₀ : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ := by
  have hk₀' : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
  have hs2 : Summable fun k : ℕ => (((k + k₀ : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ :=
    (summable_nat_add_iff k₀).2 (Real.summable_nat_rpow_inv.2 one_lt_two)
  rw [hurwitzTail_eq_tsum hk₀ (by linarith), ← tsum_mul_left]
  refine tsum_of_norm_bounded (hs2.mul_left _).hasSum fun k => ?_
  have hK : (1 : ℝ) ≤ ((k + k₀ : ℕ) : ℝ) := by
    have : 1 ≤ k + k₀ := by omega
    exact_mod_cast this
  have hK0 : (0 : ℝ) < ((k + k₀ : ℕ) : ℝ) := by linarith
  rw [show (((k + k₀ : ℕ) : ℂ)) = ((((k + k₀ : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hK0, neg_re]
  rw [← Real.rpow_neg hK0.le, show -w.re = (2 - w.re) + -2 by ring, Real.rpow_add hK0,
    Real.rpow_neg hK0.le]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (by exact_mod_cast Nat.le_add_left k₀ k)
    (by linarith)

/-- The series `∑_n a_n ζ(s+n, k₀)`. -/
noncomputable def hurwitzSeries (a : ℕ → ℂ) (k₀ : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, a n * hurwitzTail k₀ (s + n)

/-- Local bound for the terms with `n` large. -/
lemma hurwitzSeries_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : R < k₀) (s₀ : ℂ) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧
      ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1, ‖a n * hurwitzTail k₀ (s + n)‖ ≤ b n := by
  obtain ⟨C, hC⟩ := ha
  have hk₀' : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
  have hk0 : (0 : ℝ) < k₀ := by linarith
  set Z := ∑' k : ℕ, (((k + k₀ : ℕ) : ℝ) ^ (2 : ℝ))⁻¹
  have hZ : 0 ≤ Z := tsum_nonneg fun k => by positivity
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  obtain ⟨N, hN⟩ := exists_nat_ge (3 - s₀.re)
  refine ⟨N, fun n => C * Z * (k₀ : ℝ) ^ (3 - s₀.re) * (R / k₀) ^ n,
    (summable_geometric_of_lt_one (div_nonneg hR hk0.le) ((div_lt_one hk0).2 hRk)).mul_left _,
    fun n hn s hs => ?_⟩
  have hre : |s.re - s₀.re| < 1 := by
    have := Metric.mem_ball.1 hs
    rw [Complex.dist_eq] at this
    exact lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) this
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hw : 2 ≤ (s + n).re := by simp; linarith [(abs_lt.1 hre).1]
  rw [norm_mul]
  have h1 := norm_hurwitzTail_le hk₀ hw
  have h2 : (k₀ : ℝ) ^ (2 - (s + n).re) ≤ (k₀ : ℝ) ^ (3 - s₀.re) * ((k₀ : ℝ) ^ n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hk0.le, ← Real.rpow_add hk0]
    apply Real.rpow_le_rpow_of_exponent_le hk₀'
    simp; linarith [(abs_lt.1 hre).1]
  calc ‖a n‖ * ‖hurwitzTail k₀ (s + n)‖ ≤ (C * R ^ n) * ((k₀ : ℝ) ^ (3 - s₀.re) *
        ((k₀ : ℝ) ^ n)⁻¹ * Z) :=
        mul_le_mul (hC n) (h1.trans (mul_le_mul_of_nonneg_right h2 hZ)) (norm_nonneg _)
          (by positivity)
    _ = C * Z * (k₀ : ℝ) ^ (3 - s₀.re) * (R / k₀) ^ n := by rw [div_pow]; ring

/-- The poles `{1, 0, -1, …}`. -/
def notPoles : Set ℂ := {s : ℂ | ∀ n : ℕ, s ≠ 1 - n}

lemma add_nat_ne_one {s : ℂ} (hs : s ∈ notPoles) (n : ℕ) : s + n ≠ 1 := by
  intro h; exact hs n (by rw [← h]; ring)

/-- **`∑_n a_n ζ(s+n, k₀)` is holomorphic on `ℂ ∖ {1, 0, -1, …}`.** -/
theorem differentiableOn_hurwitzSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) : DifferentiableOn ℂ (hurwitzSeries a k₀) notPoles := by
  intro s₀ hs₀
  have hopen : IsOpen notPoles := isOpen_notPoles
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen s₀ hs₀
  obtain ⟨N, b, hb, hbn⟩ := hurwitzSeries_local_bound ha hR hk₀ hRk s₀
  have hr' : 0 < min r 1 := lt_min hr one_pos
  refine (differentiableAt_tsum_of_local_bound hr' (fun n => ?_) hb
    (fun n hn s hs => hbn n hn s (Metric.ball_subset_ball (min_le_right _ _) hs))
    ).differentiableWithinAt
  intro s hs
  have hs' : s ∈ notPoles := hball (Metric.ball_subset_ball (min_le_left _ _) hs)
  exact ((differentiableAt_hurwitzTail k₀ (add_nat_ne_one hs' n)).comp s
    ((differentiableAt_id).add_const _) |>.const_mul (a n)).differentiableWithinAt

/-- **Identity for `Re s > 1`**: `ζ_F^{≥k₀}(s) = ∑_n a_n ζ(s+n, k₀)`. -/
theorem zetaTail_eq_tsum_hurwitz (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ}
    (hs : 1 < s.re) : zetaTail F k₀ s = hurwitzSeries a k₀ s := by
  obtain ⟨C, hC⟩ := ha
  have hk₀' : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
  have hk0 : (0 : ℝ) < k₀ := by linarith
  have hq0 : 0 ≤ R / k₀ := div_nonneg hR hk0.le
  have hq1 : R / k₀ < 1 := (div_lt_one hk0).2 hRk
  set f : ℕ → ℕ → ℂ := fun k n => a n * ((k + k₀ : ℕ) : ℂ) ^ (-(s + n)) with hf
  have hKpos : ∀ k : ℕ, (0 : ℝ) < ((k + k₀ : ℕ) : ℝ) := fun k => by
    have : 1 ≤ k + k₀ := by omega
    exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one this
  have hnorm : ∀ k n, ‖f k n‖ ≤ C * (((k + k₀ : ℕ) : ℝ) ^ s.re)⁻¹ * (R / k₀) ^ n := by
    intro k n
    have hK := hKpos k
    have hKk : (k₀ : ℝ) ≤ ((k + k₀ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left k₀ k
    rw [hf, norm_mul, show (((k + k₀ : ℕ) : ℂ)) = ((((k + k₀ : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hK]
    simp only [neg_re, add_re, natCast_re]
    rw [Real.rpow_neg hK.le, Real.rpow_add hK, Real.rpow_natCast, mul_inv, ← mul_assoc]
    calc ‖a n‖ * (((k + k₀ : ℕ) : ℝ) ^ s.re)⁻¹ * ((((k + k₀ : ℕ) : ℝ)) ^ n)⁻¹
        ≤ (C * R ^ n) * (((k + k₀ : ℕ) : ℝ) ^ s.re)⁻¹ * ((k₀ : ℝ) ^ n)⁻¹ := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hC n) (by positivity))
            (inv_anti₀ (pow_pos hk0 n) (pow_le_pow_left₀ hk0.le hKk n)) (by positivity)
            (mul_nonneg ((norm_nonneg _).trans (hC n)) (by positivity))
      _ = C * (((k + k₀ : ℕ) : ℝ) ^ s.re)⁻¹ * (R / k₀) ^ n := by rw [div_pow]; ring
  have hsK : Summable fun k : ℕ => (((k + k₀ : ℕ) : ℝ) ^ s.re)⁻¹ :=
    (summable_nat_add_iff k₀).2 (Real.summable_nat_rpow_inv.2 hs)
  have hgeo := summable_geometric_of_lt_one hq0 hq1
  have hprod : Summable fun p : ℕ × ℕ => ‖f p.1 p.2‖ := by
    have hmaj : Summable fun p : ℕ × ℕ =>
        C * (((p.1 + k₀ : ℕ) : ℝ) ^ s.re)⁻¹ * (R / k₀) ^ p.2 := by
      have := (hsK.mul_of_nonneg hgeo (fun k => by positivity) (fun n => by positivity))
      simpa [mul_assoc] using this.mul_left C
    exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hnorm p.1 p.2) hmaj
  have hsum : Summable (Function.uncurry f) := Summable.of_norm hprod
  -- the LSeries as a double series
  have hterm : ∀ k : ℕ, LSeries.term (tail k₀ F) s (k + k₀) = ∑' n, f k n := by
    intro k
    have hK : (k + k₀ : ℕ) ≠ 0 := by omega
    rw [LSeries.term_of_ne_zero hK, tail, ite_eq_left (Nat.le_add_left k₀ k),
      hF _ (Nat.le_add_left k₀ k), evalInv, div_eq_mul_inv, ← tsum_mul_right]
    congr 1; funext n
    simp only [hf]
    rw [natCast_cpow_neg_add hK]; push_cast; ring
  have hzero : ∑ i ∈ range k₀, LSeries.term (tail k₀ F) s i = 0 := by
    refine sum_eq_zero fun i hi => ?_
    simp only [mem_range] at hi
    simp [LSeries.term, tail, show ¬ k₀ ≤ i by omega]
  have hrow : Summable fun k : ℕ => ∑' n, f k n := hsum.prod
  have hfull := (hasSum_nat_add_iff' (f := LSeries.term (tail k₀ F) s) k₀).1
    (by rw [hzero, sub_zero]; simp only [hterm]; exact hrow.hasSum)
  rw [zetaTail, LSeries, hfull.tsum_eq, hurwitzSeries]
  rw [← hsum.tsum_comm]
  congr 1; funext n
  rw [hurwitzTail_eq_tsum hk₀ (by simp; linarith [Nat.cast_nonneg (α := ℝ) n]),
    ← tsum_mul_left]

/-- On `ℂ ∖ {1, 0, -1, …}` the two continuations agree: `∑_n a_n ζ(s+n,k₀)` equals the right-hand
side of Theorem 3.2. -/
theorem hurwitzSeries_eq_splitRHS (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    Set.EqOn (hurwitzSeries a k₀) (splitRHS a k₀ u₀) notPoles := by
  have h1 := differentiableOn_hurwitzSeries ha hR hk₀ hRk
  have h2 := differentiableOn_splitRHS ha hR hRk hu₀
  have hopen : IsOpen notPoles := isOpen_notPoles
  have hconn : IsPreconnected notPoles := isConnected_notPoles.isPreconnected
  have h2' : DifferentiableOn ℂ (splitRHS a k₀ u₀) notPoles := h2
  have hs0 : (2 : ℂ) ∈ notPoles := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) n]
  refine (h1.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (h2'.analyticOnNhd hopen) hconn hs0 ?_
  have hev : ∀ᶠ s in 𝓝 (2 : ℂ), 1 < s.re := by
    have := (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (show (2 : ℂ) ∈ Complex.re ⁻¹' Set.Ioi 1 by norm_num)
    exact this
  filter_upwards [hev] with s hs
  rw [← zetaTail_eq_tsum_hurwitz (F := fun k => evalInv a k) ha hR hk₀ hRk (fun k _ => rfl) hs]
  exact zetaTail_eq_splitRHS ha hR hk₀ hRk (fun k _ => rfl) hu₀ hs

/-- `(w - 1) ζ(w, k₀) → 1` as `w → 1`. -/
lemma hurwitzTail_residue (k₀ : ℕ) :
    Tendsto (fun w => (w - 1) * hurwitzTail k₀ w) (𝓝[≠] 1) (𝓝 1) := by
  have hfin : Continuous fun w : ℂ => ∑ k ∈ Ico 1 k₀, (k : ℂ) ^ (-w) := by
    refine continuous_finsetSum _ fun k hk => ?_
    have hk0 : 0 < (k : ℂ).re := by
      simp only [mem_Ico] at hk; simp; exact_mod_cast (by omega : 0 < k)
    exact continuous_const.cpow continuous_neg (fun _ => Or.inl hk0)
  have h2 : Tendsto (fun w : ℂ => (w - 1) * ∑ k ∈ Ico 1 k₀, (k : ℂ) ^ (-w)) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun w : ℂ => (w - 1) * ∑ k ∈ Ico 1 k₀, (k : ℂ) ^ (-w)) (𝓝 1)
        (𝓝 ((1 - 1) * ∑ k ∈ Ico 1 k₀, (k : ℂ) ^ (-1 : ℂ))) :=
      ((continuous_id.sub continuous_const).mul hfin).tendsto 1
    rw [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := riemannZeta_residue_one.sub h2
  rw [sub_zero] at this
  refine this.congr fun w => ?_
  rw [hurwitzTail]; ring

/-- **Proposition 5.7, poles**: `∑_n a_n ζ(s+n, k₀)` has at `s = 1 - n` a simple pole with residue
`a_n` (a removable singularity if `a_n = 0`). -/
theorem hurwitzSeries_residue (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : R < k₀) (n : ℕ) :
    Tendsto (fun s => (s - (1 - n)) * hurwitzSeries a k₀ s) (𝓝[≠] (1 - n)) (𝓝 (a n)) := by
  set s₀ : ℂ := 1 - n with hs₀
  set T : ℕ → ℂ → ℂ := fun m s => a m * hurwitzTail k₀ (s + m) with hT
  set T' : ℕ → ℂ → ℂ := fun m s => if m = n then 0 else T m s with hT'
  obtain ⟨N, b, hb, hbn⟩ := hurwitzSeries_local_bound ha hR hk₀ hRk s₀
  -- points of the punctured half-ball avoid the poles `1 - m`, `m ≠ n`
  have hfar : ∀ s ∈ Metric.ball s₀ (1 / 2), ∀ m : ℕ, m ≠ n → s + m ≠ 1 := by
    intro s hs m hm h
    have hs' : s = 1 - m := by rw [← h]; ring
    have hd := Metric.mem_ball.1 hs
    rw [hs', hs₀, Complex.dist_eq, show (1 : ℂ) - m - (1 - n) = ((n : ℤ) - m : ℤ) by push_cast; ring,
      Complex.norm_intCast] at hd
    have : (n : ℤ) - m ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hm.symm)
    have : (1 : ℝ) ≤ |(((n : ℤ) - m : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs this
    linarith
  -- the remaining series is holomorphic at `s₀`
  have hG : DifferentiableAt ℂ (fun s => ∑' m, T' m s) s₀ := by
    refine differentiableAt_tsum_of_local_bound (r := 1 / 2) (N := N) (by norm_num) (fun m => ?_) hb
      (fun m hm s hs => ?_)
    · intro s hs
      by_cases hmn : m = n
      · simp only [hT', hmn, ite_true]; exact differentiableWithinAt_const _
      · simp only [hT', hmn, ite_false, hT]
        exact ((differentiableAt_hurwitzTail k₀ (hfar s hs m hmn)).comp s
          ((differentiableAt_id).add_const _) |>.const_mul (a m)).differentiableWithinAt
    · have hs1 : s ∈ Metric.ball s₀ 1 := Metric.ball_subset_ball (by norm_num) hs
      by_cases hmn : m = n
      · have := hbn m hm s hs1
        simp only [hT', hmn, ite_true, norm_zero] at this ⊢
        exact (norm_nonneg _).trans this
      · simp only [hT', hmn, ite_false]; exact hbn m hm s hs1
  have hGlim : Tendsto (fun s => (s - s₀) * ∑' m, T' m s) (𝓝[≠] s₀) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℂ => (s - s₀) * ∑' m, T' m s) s₀ :=
      ((continuousAt_id.sub continuousAt_const).mul hG.continuousAt)
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- the term `m = n`
  have hTn : Tendsto (fun s => (s - s₀) * T n s) (𝓝[≠] s₀) (𝓝 (a n)) := by
    have hmap : Tendsto (fun s : ℂ => s + n) (𝓝[≠] s₀) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((continuous_id.add continuous_const).tendsto s₀ (f := fun s : ℂ => s + n))
        rw [hs₀, sub_add_cancel] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        intro h; apply hs
        rw [Set.mem_singleton_iff] at h ⊢; rw [hs₀]; linear_combination h
    have := ((hurwitzTail_residue k₀).comp hmap).const_mul (a n)
    rw [mul_one] at this
    refine this.congr fun s => ?_
    simp only [Function.comp, hT, hs₀]; ring
  -- splitting off the term `m = n`
  have heq : ∀ᶠ s in 𝓝[≠] s₀, (s - s₀) * hurwitzSeries a k₀ s =
      (s - s₀) * T n s + (s - s₀) * ∑' m, T' m s := by
    have hball : Metric.ball s₀ (1 / 2) ∈ 𝓝[≠] s₀ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [hball, self_mem_nhdsWithin] with s hs hne
    have hsum : Summable fun m => T m s := by
      refine Summable.of_norm_bounded_eventually hb ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop N] with m hm
      exact hbn m hm s (Metric.ball_subset_ball (by norm_num) hs)
    rw [hurwitzSeries, show (fun m => a m * hurwitzTail k₀ (s + m)) = fun m => T m s from rfl,
      hsum.tsum_eq_add_tsum_ite n, mul_add]
  have := (hTn.add hGlim).congr' (EventuallyEq.symm heq)
  rwa [add_zero] at this

lemma mem_notPoles_of_near {n : ℕ} {s : ℂ} (hs : s ∈ Metric.ball ((1 : ℂ) - n) (1 / 2))
    (hne : s ≠ 1 - n) : s ∈ notPoles := by
  intro m hm
  by_cases hmn : m = n
  · exact hne (hmn ▸ hm)
  · have hd := Metric.mem_ball.1 hs
    rw [hm, Complex.dist_eq, show (1 : ℂ) - m - (1 - n) = ((n : ℤ) - m : ℤ) by push_cast; ring,
      Complex.norm_intCast] at hd
    have : (n : ℤ) - m ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm hmn)
    have : (1 : ℝ) ≤ |(((n : ℤ) - m : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs this
    linarith

/-- **Residues of `ζ_F^{≥k₀}`**: the continuation of Theorem 3.2 has residue `a_n` at `s = 1 - n`. -/
theorem splitRHS_residue (ha : GeomBounded a R) (hR : 0 ≤ R) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hRk : R < k₀) {u₀ : ℝ} (hu₀ : 0 < u₀) (n : ℕ) :
    Tendsto (fun s => (s - (1 - n)) * splitRHS a k₀ u₀ s) (𝓝[≠] (1 - n)) (𝓝 (a n)) := by
  refine (hurwitzSeries_residue ha hR hk₀ hRk n).congr' ?_
  have hball : Metric.ball ((1 : ℂ) - n) (1 / 2) ∈ 𝓝[≠] ((1 : ℂ) - n) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by norm_num))
  filter_upwards [hball, self_mem_nhdsWithin] with s hs hne
  rw [hurwitzSeries_eq_splitRHS ha hR hk₀ hRk hu₀ (mem_notPoles_of_near hs hne)]

end ZetaF
