/-
# Formula (K2) for Khinchin's constant (Section 6)

`log K = ∑_{k ≥ 1} μ_k log k` and, by summation by parts,
`log K · log 2 = ∑_{k ≥ 2} -log(1 - 1/k) log(1 + 1/k)`.
-/
import ZetaF.Khinchin.ZetaZ

open Filter Topology Real Finset

namespace ZetaF

/-- `log K = ∑_{k ≥ 1} μ_k log k`, so that Khinchin's constant is `K = exp logK`. -/
noncomputable def logK : ℝ := ∑' k : ℕ, gkMu (k + 1) * Real.log (k + 1)

/-- The summand of (K2), `F(k+2) = -log(1 - 1/(k+2)) log(1 + 1/(k+2))`. -/
noncomputable def khF (k : ℕ) : ℝ :=
  -(Real.log (1 - 1 / ((k : ℝ) + 2)) * Real.log (1 + 1 / ((k : ℝ) + 2)))

lemma log_one_sub_inv_add_two (k : ℕ) :
    Real.log (1 - 1 / ((k : ℝ) + 2)) = Real.log ((k : ℝ) + 1) - Real.log ((k : ℝ) + 2) := by
  have h1 : (0 : ℝ) < k + 1 := by positivity
  have h2 : (0 : ℝ) < k + 2 := by positivity
  rw [show 1 - 1 / ((k : ℝ) + 2) = (k + 1) / (k + 2) by field_simp; ring,
    Real.log_div h1.ne' h2.ne']

lemma log_one_add_inv_add_two (k : ℕ) :
    Real.log (1 + 1 / ((k : ℝ) + 2)) = Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2) := by
  have h3 : (0 : ℝ) < k + 3 := by positivity
  have h2 : (0 : ℝ) < k + 2 := by positivity
  rw [show 1 + 1 / ((k : ℝ) + 2) = (k + 3) / (k + 2) by field_simp; ring,
    Real.log_div h3.ne' h2.ne']

lemma gkMu_mul_log_two (k : ℕ) :
    gkMu (k + 1) * Real.log 2 =
      2 * Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) - Real.log ((k : ℝ) + 3) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [gkMu, log_gk, div_mul_cancel₀ _ hl.ne']

lemma gkMu_nonneg (k : ℕ) : 0 ≤ gkMu (k + 1) := by
  unfold gkMu
  have h0 : (0 : ℝ) ≤ 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) + 2)) := by positivity
  exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))

lemma logK_term_nonneg (k : ℕ) : 0 ≤ gkMu (k + 1) * Real.log (k + 1) :=
  mul_nonneg (gkMu_nonneg k) (Real.log_nonneg (by have := k.cast_nonneg (α := ℝ); linarith))

lemma khF_eq (k : ℕ) : khF k =
    (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) *
      (Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2)) := by
  rw [khF, log_one_sub_inv_add_two, log_one_add_inv_add_two]; ring

lemma khF_nonneg (k : ℕ) : 0 ≤ khF k := by
  rw [khF_eq]
  apply mul_nonneg <;> rw [sub_nonneg] <;>
    exact Real.log_le_log (by positivity) (by linarith)

/-- `0 ≤ log(1 + 1/(k+2)) ≤ 1/(k+2)`. -/
lemma log_one_add_inv_le (k : ℕ) :
    Real.log (1 + 1 / ((k : ℝ) + 2)) ≤ 1 / ((k : ℝ) + 2) := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / ((k : ℝ) + 2) by positivity)
  linarith

lemma khF_le (k : ℕ) : khF k ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
  have h1 : (0 : ℝ) < k + 1 := by positivity
  have h2 : (0 : ℝ) < k + 2 := by positivity
  -- `-log(1 - 1/(k+2)) = log((k+2)/(k+1)) ≤ 1/(k+1)`
  have ha : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    rw [← Real.log_div h2.ne' h1.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k + 2) / (k + 1) by positivity)
    have e : ((k : ℝ) + 2) / (k + 1) - 1 = 1 / (k + 1) := by field_simp; ring
    linarith
  have hb : Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) := by
    rw [← log_one_add_inv_add_two]
    refine (log_one_add_inv_le k).trans ?_
    exact one_div_le_one_div_of_le h1 (by linarith)
  have ha0 : 0 ≤ Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) :=
    sub_nonneg.2 (Real.log_le_log h1 (by linarith))
  have hb0 : 0 ≤ Real.log ((k : ℝ) + 3) - Real.log ((k : ℝ) + 2) :=
    sub_nonneg.2 (Real.log_le_log h2 (by linarith))
  rw [khF_eq]
  calc _ ≤ 1 / ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) := mul_le_mul ha hb hb0 (by positivity)
    _ = _ := by rw [one_div_mul_one_div, sq]

lemma summable_khF : Summable khF := by
  refine Summable.of_nonneg_of_le khF_nonneg khF_le ?_
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  exact this.congr fun k => by push_cast; rfl

/-- Summation by parts:
`∑_{2 ≤ k ≤ N+1} F(k) = log 2 ∑_{k ≤ N+1} μ_k log k + log(1 + 1/(N+2)) log(N+1)`. -/
lemma sum_khF_eq (N : ℕ) :
    ∑ i ∈ range N, khF i =
      (∑ j ∈ range (N + 1), gkMu (j + 1) * Real.log (j + 1)) * Real.log 2 +
        (Real.log ((N : ℝ) + 3) - Real.log ((N : ℝ) + 2)) * Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e := gkMu_mul_log_two (N + 1)
    have c1 : ((N + 1 : ℕ) : ℝ) + 1 = N + 2 := by push_cast; ring
    have c2 : ((N + 1 : ℕ) : ℝ) + 2 = N + 3 := by push_cast; ring
    have c3 : ((N + 1 : ℕ) : ℝ) + 3 = N + 4 := by push_cast; ring
    rw [c1, c2, c3] at e
    rw [sum_range_succ, ih, sum_range_succ (n := N + 1), khF_eq, c1, c2, c3]
    linear_combination -Real.log ((N : ℝ) + 2) * e

lemma logK_summable : Summable fun k : ℕ => gkMu (k + 1) * Real.log (k + 1) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  refine summable_of_sum_range_le (c := (∑' k, khF k) / Real.log 2) logK_term_nonneg fun n => ?_
  rw [le_div_iff₀ hl]
  have hrest : 0 ≤ (Real.log ((n : ℝ) + 3) - Real.log ((n : ℝ) + 2)) * Real.log ((n : ℝ) + 1) := by
    apply mul_nonneg
    · exact sub_nonneg.2 (Real.log_le_log (by positivity) (by linarith))
    · exact Real.log_nonneg (by have := n.cast_nonneg (α := ℝ); linarith)
  have h1 : ∑ j ∈ range n, gkMu (j + 1) * Real.log (j + 1) ≤
      ∑ j ∈ range (n + 1), gkMu (j + 1) * Real.log (j + 1) :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.le_succ n))
      fun j _ _ => logK_term_nonneg j
  have h2 := sum_khF_eq n
  have h3 : ∑ i ∈ range n, khF i ≤ ∑' k, khF k :=
    summable_khF.sum_le_tsum _ fun i _ => khF_nonneg i
  nlinarith

lemma hasSum_logK : HasSum (fun k : ℕ => gkMu (k + 1) * Real.log (k + 1)) logK :=
  logK_summable.hasSum

lemma tendsto_remainder :
    Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 3) - Real.log ((N : ℝ) + 2)) *
      Real.log ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) ^ 1 / (1 * ((N : ℝ) + 1) + 1))
      atTop (𝓝 0) :=
    (tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun N => ?_) fun N => ?_
  · apply mul_nonneg
    · exact sub_nonneg.2 (Real.log_le_log (by positivity) (by linarith))
    · exact Real.log_nonneg (by have := N.cast_nonneg (α := ℝ); linarith)
  · have hlog : 0 ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_nonneg (by have := N.cast_nonneg (α := ℝ); linarith)
    have h := log_one_add_inv_le N
    rw [log_one_add_inv_add_two] at h
    simp only [pow_one, one_mul]
    rw [show (N : ℝ) + 1 + 1 = N + 2 by ring, div_eq_mul_one_div, mul_comm (Real.log _)]
    exact mul_le_mul_of_nonneg_right h hlog

/-- **(K2)**: `log K · log 2 = ∑_{k ≥ 2} -log(1 - 1/k) log(1 + 1/k)`. -/
theorem hasSum_khF : HasSum khF (logK * Real.log 2) := by
  have h1 : Tendsto (fun N : ℕ => ∑ i ∈ range N, khF i) atTop (𝓝 (logK * Real.log 2 + 0)) := by
    rw [funext sum_khF_eq]
    refine Tendsto.add ?_ tendsto_remainder
    exact (hasSum_logK.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).mul_const _
  rw [add_zero] at h1
  have hs := summable_khF.hasSum
  rwa [tendsto_nhds_unique hs.tendsto_sum_nat h1] at hs

/-- **(K2)**, in the form of the paper. -/
theorem logK_mul_log_two :
    logK * Real.log 2 = ∑' k : ℕ, -(Real.log (1 - 1 / (k + 2)) * Real.log (1 + 1 / (k + 2))) :=
  hasSum_khF.tsum_eq.symm

end ZetaF
