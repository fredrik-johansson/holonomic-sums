/-
# Lemma 6.2 (Bailey–Borwein–Crandall): the dilogarithm series for `log K`

`log K · log 2 = log² 2 + Li₂(-1/2) + ½ ∑_{k ≥ 2} (-1)^k Li₂(4/k²)`,

proved from (K2) as in the paper: dilation, duplication, Landen's identity and telescoping.
Indices are shifted: the Lean index `k : ℕ` corresponds to the paper's `k + 2`.
-/
import ZetaF.Khinchin.Dilog

open Filter Topology Real Set Finset

namespace ZetaF

/-- The paper's `g(k) = f(1/k) - Li₂(1/k²) + ½ Li₂(4/k²)` at `k = y + 2`. -/
noncomputable def bbcG (y : ℝ) : ℝ :=
  -(Real.log (1 - 1 / (y + 2)) * Real.log (1 + 1 / (y + 2))) - Li₂ (1 / (y + 2) ^ 2) +
    1 / 2 * Li₂ (4 / (y + 2) ^ 2)

/-- `P(y) = d_{y+2} d_{y+3} + ½ d_{y+2}²` with `d_k = log(k/(k-1))`; `Λ_{y+3} = P(y+1) - P(y)`. -/
noncomputable def bbcP (y : ℝ) : ℝ :=
  (Real.log (y + 2) - Real.log (y + 1)) * (Real.log (y + 3) - Real.log (y + 2)) +
    1 / 2 * (Real.log (y + 2) - Real.log (y + 1)) ^ 2

/-- **Telescoping form of `g(k)`, `k ≥ 3`** (the paper's display after Landen's identity). -/
lemma bbcG_succ {y : ℝ} (hy : 0 ≤ y) :
    bbcG (y + 1) = -2 * (Li₂ (-1 / (y + 3)) - Li₂ (-1 / (y + 2))) +
      (Li₂ (-2 / (y + 3)) - Li₂ (-2 / (y + 1))) + (bbcP (y + 1) - bbcP y) := by
  have h1 : 0 < y + 1 := by linarith
  have h2 : 0 < y + 2 := by linarith
  have h3 : 0 < y + 3 := by linarith
  have h4 : 0 < y + 4 := by linarith
  -- logarithms
  have l1 : Real.log (1 - 1 / (y + 3)) = Real.log (y + 2) - Real.log (y + 3) := by
    rw [show 1 - 1 / (y + 3) = (y + 2) / (y + 3) by field_simp; ring, Real.log_div h2.ne' h3.ne']
  have l2 : Real.log (1 + 1 / (y + 3)) = Real.log (y + 4) - Real.log (y + 3) := by
    rw [show 1 + 1 / (y + 3) = (y + 4) / (y + 3) by field_simp; ring, Real.log_div h4.ne' h3.ne']
  have l3 : Real.log (1 - 2 / (y + 3)) = Real.log (y + 1) - Real.log (y + 3) := by
    rw [show 1 - 2 / (y + 3) = (y + 1) / (y + 3) by field_simp; ring, Real.log_div h1.ne' h3.ne']
  -- duplication at `1/k` and `2/k`
  have dupA := Li₂_add_Li₂_neg (x := 1 / (y + 3)) (by
    rw [abs_of_pos (by positivity), div_le_one h3]; linarith)
  rw [div_pow, one_pow, ← neg_div] at dupA
  have dupB := Li₂_add_Li₂_neg (x := 2 / (y + 3)) (by
    rw [abs_of_pos (by positivity), div_le_one h3]; linarith)
  rw [div_pow, ← neg_div, show (2 : ℝ) ^ 2 = 4 by norm_num] at dupB
  -- Landen at `z = 1/k` and `z = 2/k`
  have lanA := Li₂_landen (z := 1 / (y + 3)) (by rw [div_lt_one h3]; linarith)
  have eA : 1 / (y + 3) - 1 = -(y + 2) / (y + 3) := by field_simp; ring
  rw [eA, div_div_div_cancel_right₀ h3.ne', div_neg, ← neg_div, l1] at lanA
  have lanB := Li₂_landen (z := 2 / (y + 3)) (by rw [div_lt_one h3]; linarith)
  have eB : 2 / (y + 3) - 1 = -(y + 1) / (y + 3) := by field_simp; ring
  rw [eB, div_div_div_cancel_right₀ h3.ne', div_neg, ← neg_div, l3] at lanB
  unfold bbcG bbcP
  rw [show y + 1 + 2 = y + 3 by ring, show y + 1 + 1 = y + 2 by ring,
    show y + 1 + 3 = y + 4 by ring, l1, l2]
  linear_combination 2 * dupA - dupB - 2 * lanA + lanB

/-- The telescoped partial sums. -/
noncomputable def bbcQ (y : ℝ) : ℝ :=
  -2 * (Li₂ (-1 / (y + 2)) - Li₂ (-1 / 2)) +
    (Li₂ (-2 / (y + 2)) + Li₂ (-2 / (y + 1)) - Li₂ (-2) - Li₂ (-1)) + (bbcP y - bbcP 0)

lemma bbcQ_succ {y : ℝ} (hy : 0 ≤ y) : bbcQ (y + 1) = bbcQ y + bbcG (y + 1) := by
  rw [bbcG_succ hy]
  unfold bbcQ
  rw [show y + 1 + 2 = y + 3 by ring, show y + 1 + 1 = y + 2 by ring]
  ring

lemma sum_bbcG (N : ℕ) : ∑ i ∈ range N, bbcG ((i : ℝ) + 1) = bbcQ N := by
  induction N with
  | zero => simp [bbcQ]
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.cast_succ, bbcQ_succ N.cast_nonneg]

lemma tendsto_Li₂_div (c a : ℝ) :
    Tendsto (fun N : ℕ => Li₂ (c / ((N : ℝ) + a))) atTop (𝓝 0) := by
  have hc : ContinuousAt Li₂ 0 := (hasDerivAt_Li₂ (by norm_num)).continuousAt
  have h0 : Tendsto (fun N : ℕ => c / ((N : ℝ) + a)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)
  have := hc.tendsto.comp h0
  rwa [Li₂_zero] at this

lemma tendsto_log_succ_sub (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + a + 1) - Real.log ((N : ℝ) + a)) atTop (𝓝 0) :=
  (Real.tendsto_log_comp_add_sub_log 1).comp
    (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop)

lemma tendsto_bbcP : Tendsto (fun N : ℕ => bbcP N) atTop (𝓝 0) := by
  have hA : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_log_succ_sub 1).congr fun N => by ring_nf
  have hB : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 3) - Real.log ((N : ℝ) + 2)) atTop (𝓝 0) :=
    (tendsto_log_succ_sub 2).congr fun N => by ring_nf
  have := (hA.mul hB).add ((hA.pow 2).const_mul (1 / 2))
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at this
  exact this

lemma tendsto_bbcQ : Tendsto (fun N : ℕ => bbcQ N) atTop
    (𝓝 (-2 * (0 - Li₂ (-1 / 2)) + (0 + 0 - Li₂ (-2) - Li₂ (-1)) + (0 - bbcP 0))) := by
  unfold bbcQ
  refine Tendsto.add (Tendsto.add ?_ ?_) (tendsto_bbcP.sub tendsto_const_nhds)
  · exact ((tendsto_Li₂_div (-1) 2).sub tendsto_const_nhds).const_mul _
  · exact (((tendsto_Li₂_div (-2) 2).add (tendsto_Li₂_div (-2) 1)).sub
      tendsto_const_nhds).sub tendsto_const_nhds

/-! ### Summability -/

lemma summable_Li₂_div_sq {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 4) :
    Summable fun k : ℕ => Li₂ (c / ((k : ℝ) + 2) ^ 2) := by
  have hs : Summable fun k : ℕ => c * (π ^ 2 / 6) * (1 / ((k : ℝ) + 2) ^ 2) := by
    have := (summable_nat_add_iff 2).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    exact (this.congr fun k => by push_cast; rfl).mul_left _
  refine Summable.of_norm_bounded hs fun k => ?_
  have hk : (4 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith [k.cast_nonneg (α := ℝ)]
  have hpos : (0 : ℝ) < ((k : ℝ) + 2) ^ 2 := by positivity
  have hx : |c / ((k : ℝ) + 2) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hpos]; linarith
  rw [Real.norm_eq_abs]
  refine (abs_Li₂_le hx).trans (le_of_eq ?_)
  rw [abs_of_nonneg (by positivity)]
  ring

lemma summable_bbcG : Summable fun k : ℕ => bbcG k :=
  ((summable_khF.sub (summable_Li₂_div_sq zero_le_one (by norm_num))).add
    ((summable_Li₂_div_sq (by norm_num) le_rfl).mul_left (1 / 2))).congr fun k => by
      simp only [bbcG, khF]

/-! ### The sum of `g` -/

lemma bbcG_zero : bbcG 0 = Real.log 2 * (Real.log 3 - Real.log 2) - Li₂ (1 / 4) + π ^ 2 / 12 := by
  unfold bbcG
  rw [show (0 : ℝ) + 2 = 2 by norm_num, show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num,
    show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, show (1 : ℝ) / 2 ^ 2 = 1 / 4 by norm_num,
    show (4 : ℝ) / 2 ^ 2 = 1 by norm_num, Real.log_inv, Real.log_div (by norm_num) (by norm_num),
    Li₂_one]
  ring

/-- `∑_{k ≥ 2} g(k) = log² 2 + Li₂(-1/2) + π²/6`. -/
theorem hasSum_bbcG :
    HasSum (fun k : ℕ => bbcG k) (Real.log 2 ^ 2 + Li₂ (-1 / 2) + π ^ 2 / 6) := by
  have hs1 : Summable fun i : ℕ => bbcG ((i : ℝ) + 1) :=
    ((summable_nat_add_iff 1).2 summable_bbcG).congr fun i => by rw [Nat.cast_succ]
  have hlim : Tendsto (fun N : ℕ => ∑ i ∈ range N, bbcG ((i : ℝ) + 1)) atTop
      (𝓝 (-2 * (0 - Li₂ (-1 / 2)) + (0 + 0 - Li₂ (-2) - Li₂ (-1)) + (0 - bbcP 0))) := by
    rw [funext sum_bbcG]; exact tendsto_bbcQ
  have h1 := hs1.hasSum
  rw [tendsto_nhds_unique h1.tendsto_sum_nat hlim] at h1
  have h1' : HasSum (fun i : ℕ => bbcG ((i + 1 : ℕ) : ℝ))
      (-2 * (0 - Li₂ (-1 / 2)) + (0 + 0 - Li₂ (-2) - Li₂ (-1)) + (0 - bbcP 0)) :=
    h1.congr_fun fun i => by rw [Nat.cast_succ]
  have h2 := (hasSum_nat_add_iff (f := fun k : ℕ => bbcG k) 1).1 h1'
  rw [range_one, sum_singleton, Nat.cast_zero, bbcG_zero] at h2
  have hval : -2 * (0 - Li₂ (-1 / 2)) + (0 + 0 - Li₂ (-2) - Li₂ (-1)) + (0 - bbcP 0) +
      (Real.log 2 * (Real.log 3 - Real.log 2) - Li₂ (1 / 4) + π ^ 2 / 12) =
      Real.log 2 ^ 2 + Li₂ (-1 / 2) + π ^ 2 / 6 := by
    have hP : bbcP 0 = Real.log 2 * (Real.log 3 - Real.log 2) + 1 / 2 * Real.log 2 ^ 2 := by
      unfold bbcP; norm_num
    rw [hP, Li₂_neg_two, Li₂_neg_one, Li₂_quarter, Li₂_half]
    ring
  rwa [hval] at h2

/-! ### Dilation -/

/-- **Dilation**: `½ ∑_{k ≥ 2} (-1)^k Li₂(4/k²) = π²/6 + ∑_{k ≥ 2} (Li₂(1/k²) - ½ Li₂(4/k²))`. -/
theorem dilation :
    1 / 2 * ∑' k : ℕ, (-1 : ℝ) ^ k * Li₂ (4 / ((k : ℝ) + 2) ^ 2) =
      Li₂ 1 + ∑' k : ℕ, Li₂ (1 / ((k : ℝ) + 2) ^ 2) -
        1 / 2 * ∑' k : ℕ, Li₂ (4 / ((k : ℝ) + 2) ^ 2) := by
  set B : ℕ → ℝ := fun k => Li₂ (4 / ((k : ℝ) + 2) ^ 2) with hB
  have hBs : Summable B := summable_Li₂_div_sq (by norm_num) le_rfl
  have hinj2 : Function.Injective fun m : ℕ => 2 * m := fun a b h => by simpa using h
  have hinj2' : Function.Injective fun m : ℕ => 2 * m + 1 := fun a b h => by simpa using h
  have he : Summable fun m : ℕ => B (2 * m) := hBs.comp_injective hinj2
  have ho : Summable fun m : ℕ => B (2 * m + 1) := hBs.comp_injective hinj2'
  have hB_eo : HasSum B (∑' m, B (2 * m) + ∑' m, B (2 * m + 1)) :=
    HasSum.even_add_odd (f := B) he.hasSum ho.hasSum
  have hfe : HasSum (fun m : ℕ => (-1 : ℝ) ^ (2 * m) * B (2 * m)) (∑' m, B (2 * m)) :=
    he.hasSum.congr_fun fun m => by rw [pow_mul]; simp
  have hfo : HasSum (fun m : ℕ => (-1 : ℝ) ^ (2 * m + 1) * B (2 * m + 1))
      (-∑' m, B (2 * m + 1)) :=
    ho.hasSum.neg.congr_fun fun m => by rw [pow_succ, pow_mul]; simp
  have hf_eo : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * B k)
      (∑' m, B (2 * m) + -∑' m, B (2 * m + 1)) :=
    HasSum.even_add_odd (f := fun k : ℕ => (-1 : ℝ) ^ k * B k) hfe hfo
  -- the even terms: `B (2m) = Li₂ (1/(m+1)²)`
  have heven : ∀ m : ℕ, B (2 * m) = Li₂ (1 / ((m : ℝ) + 1) ^ 2) := fun m => by
    simp only [hB]
    congr 1
    push_cast
    field_simp
    ring
  have hC : Summable fun m : ℕ => Li₂ (1 / ((m : ℝ) + 1) ^ 2) := he.congr heven
  have hCs : ∑' m : ℕ, Li₂ (1 / ((m : ℝ) + 1) ^ 2) =
      Li₂ 1 + ∑' k : ℕ, Li₂ (1 / ((k : ℝ) + 2) ^ 2) := by
    have hshift : ∀ k : ℕ, Li₂ (1 / (((k + 1 : ℕ) : ℝ) + 1) ^ 2) = Li₂ (1 / ((k : ℝ) + 2) ^ 2) :=
      fun k => by rw [Nat.cast_succ, add_assoc, one_add_one_eq_two]
    rw [hC.tsum_eq_zero_add, tsum_congr hshift, Nat.cast_zero, zero_add, one_pow, div_one]
  have e1 : ∑' m, B (2 * m) = Li₂ 1 + ∑' k : ℕ, Li₂ (1 / ((k : ℝ) + 2) ^ 2) := by
    rw [tsum_congr heven, hCs]
  rw [hf_eo.tsum_eq, hB_eo.tsum_eq, e1]
  ring

/-! ### Lemma 6.2 -/

/-- **Lemma 6.2** (Bailey–Borwein–Crandall):
`log K · log 2 = log² 2 + Li₂(-1/2) + ½ ∑_{k ≥ 2} (-1)^k Li₂(4/k²)`. -/
theorem logK_mul_log_two_eq_dilog :
    logK * Real.log 2 =
      Real.log 2 ^ 2 + Li₂ (-1 / 2) + 1 / 2 * ∑' k : ℕ, (-1) ^ k * Li₂ (4 / (k + 2) ^ 2) := by
  have hA := summable_Li₂_div_sq zero_le_one (by norm_num)
  have hB := summable_Li₂_div_sq (by norm_num) le_rfl
  have hK : logK * Real.log 2 = ∑' k : ℕ, (bbcG k + Li₂ (1 / ((k : ℝ) + 2) ^ 2) -
      1 / 2 * Li₂ (4 / ((k : ℝ) + 2) ^ 2)) := by
    rw [← hasSum_khF.tsum_eq]
    exact tsum_congr fun k => by unfold bbcG khF; ring
  rw [hK, (summable_bbcG.add hA).tsum_sub (hB.mul_left _), summable_bbcG.tsum_add hA,
    tsum_mul_left, hasSum_bbcG.tsum_eq, dilation, Li₂_one]
  ring

end ZetaF
