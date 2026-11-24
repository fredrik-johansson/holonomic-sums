/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Section 6.4.2, remaining error bounds for Algorithm K3

* **Omitted terms**: the tails `∑_{k ≥ k₁} I_k` and `∑_{m ≥ m₁} J_m` are at most twice the bound for
  their first term, once consecutive bounds shrink by a factor `2` (`e^{-(2k₁+1)U} ≤ ½`,
  `e^{-π²(2m₁+2)/U} ≤ ½`).
* **The `k`-series**: with `x = κU`, the `n`-th term `t_n = (4/κ)^n e^{-x} e_n(x)/n²` of
  `I_k = ∑ t_n` is at most `τ_n = (4/κ)^n min(1, n x^{n-1} e^{-x}/(n-1)!)/n²` for `n - 1 ≤ x`, and at most
  `(4/κ)^n/n²` always; for `κ ≥ 9` and `U ≤ ¼` the tail from `N` is at most
  `2τ_N + (9/5)(4/κ)^{n₁}/n₁²` with `n₁ = ⌈x⌉ + 1`.
* **Main term and constants**: the `n`-th term of `M` is at most `(5/2)(4U)^n/(n² n!)` in absolute
  value (which implies the paper's `3(8U)^n/n!`), its tails are at most twice the first such bound
  once `4U ≤ (N+1)/2`, and the tail of `Li₂(1/9) = ∑ 9^{-n}/n²` after `N` terms is at most `9^{-N}`.
-/
import ZetaF.Khinchin.K3Closed

open MeasureTheory Set Filter Real
open scoped Nat Topology

namespace ZetaF.K3Bounds

open ZetaF.K3Closed

/-! ### Omitted terms -/

lemma dualTermK_nonneg {U c : ℝ} : 0 ≤ dualTermK U c := by
  unfold dualTermK
  refine mul_nonneg (Real.sqrt_nonneg _) (setIntegral_nonneg measurableSet_Ioc (fun u hu => ?_))
  exact mul_nonneg (mul_nonneg (rpow_nonneg hu.1.le _) (exp_pos _).le) (kerG_nonneg hu.1.le)

/-- The bound `e^{-(k²-4)U}/((k²-4)U)` for `I_k`. -/
noncomputable def kBound (U : ℝ) (k : ℕ) : ℝ := rexp (-((k : ℝ) ^ 2 - 4) * U) / (((k : ℝ) ^ 2 - 4) * U)

lemma kBound_pos {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : 3 ≤ k) : 0 < kBound U k := by
  have : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold kBound
  exact div_pos (exp_pos _) (mul_pos (by nlinarith) hU)

lemma kBound_ratio {U : ℝ} (hU : 0 < U) {k₁ : ℕ} (hk₁ : 3 ≤ k₁)
    (hE : rexp (-((2 * k₁ + 1) * U)) ≤ 1 / 2) {k : ℕ} (hk : k₁ ≤ k) :
    kBound U (k + 1) ≤ kBound U k / 2 := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk₁.trans hk
  have hkk : (k₁ : ℝ) ≤ k := by exact_mod_cast hk
  have hA : 0 < (k : ℝ) ^ 2 - 4 := by nlinarith
  have hB : (k : ℝ) ^ 2 - 4 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 - 4 := by push_cast; nlinarith
  have hE' : rexp (-((2 * k + 1) * U)) ≤ 1 / 2 :=
    (exp_le_exp.2 (by nlinarith)).trans hE
  unfold kBound
  have hsplit : rexp (-(((k + 1 : ℕ) : ℝ) ^ 2 - 4) * U) =
      rexp (-((k : ℝ) ^ 2 - 4) * U) * rexp (-((2 * k + 1) * U)) := by
    rw [← exp_add]; push_cast; ring_nf
  rw [hsplit]
  calc rexp (-((k : ℝ) ^ 2 - 4) * U) * rexp (-((2 * k + 1) * U)) / ((((k + 1 : ℕ) : ℝ) ^ 2 - 4) * U)
      ≤ rexp (-((k : ℝ) ^ 2 - 4) * U) * (1 / 2) / (((k : ℝ) ^ 2 - 4) * U) := by
        gcongr
    _ = _ := by ring

/-- **Tail of the `k`-sum**: `∑_{k ≥ k₁} I_k ≤ 2 e^{-(k₁²-4)U}/((k₁²-4)U)` once
`e^{-(2k₁+1)U} ≤ ½`. -/
theorem kTail_le {U : ℝ} (hU : 0 < U) {k₁ : ℕ} (hk₁ : 3 ≤ k₁)
    (hE : rexp (-((2 * k₁ + 1) * U)) ≤ 1 / 2) :
    Summable (fun i => kTermK U (k₁ + i)) ∧ ∑' i, kTermK U (k₁ + i) ≤ 2 * kBound U k₁ := by
  have h := tail_le_two_mul (fun k => kBound U k) k₁ (fun k hk => by
    rw [Real.norm_of_nonneg (kBound_pos hU (hk₁.trans (Nat.le_succ_of_le hk))).le,
      Real.norm_of_nonneg (kBound_pos hU (hk₁.trans hk)).le]
    exact kBound_ratio hU hk₁ hE hk)
  rw [Real.norm_of_nonneg (kBound_pos hU hk₁).le] at h
  have hle : ∀ i, kTermK U (k₁ + i) ≤ kBound U (k₁ + i) :=
    fun i => kTermK_le hU (hk₁.trans (Nat.le_add_right _ _))
  have hnn : ∀ i, 0 ≤ kTermK U (k₁ + i) :=
    fun i => (kTermK_pos hU (hk₁.trans (Nat.le_add_right _ _))).le
  have hs : Summable (fun i => kTermK U (k₁ + i)) := Summable.of_nonneg_of_le hnn hle h.1
  refine ⟨hs, ?_⟩
  have h2 := h.2
  rw [Real.norm_of_nonneg (tsum_nonneg fun i => (kBound_pos hU
    (hk₁.trans (Nat.le_add_right _ _))).le)] at h2
  exact (hs.tsum_le_tsum hle h.1).trans h2

/-- The bound `2√(πU) G(U) e^{-π²(m+½)²/U}` for `J_m`. -/
noncomputable def mBound (U : ℝ) (m : ℕ) : ℝ :=
  2 * √(π * U) * kerG U * rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / U))

lemma mBound_nonneg {U : ℝ} (hU : 0 < U) (m : ℕ) : 0 ≤ mBound U m := by
  unfold mBound
  have := kerG_nonneg hU.le
  positivity

/-- **Tail of the `m`-sum**: `∑_{m ≥ m₁} J_m ≤ 2 · 2√(πU) G(U) e^{-π²(m₁+½)²/U}` once
`e^{-π²(2m₁+2)/U} ≤ ½`. -/
theorem mTail_le {U : ℝ} (hU : 0 < U) {m₁ : ℕ}
    (hE : rexp (-(π ^ 2 * (2 * m₁ + 2) / U)) ≤ 1 / 2) :
    Summable (fun i => dualTermK U (π ^ 2 * (((m₁ + i : ℕ) : ℝ) + 1 / 2) ^ 2)) ∧
      ∑' i, dualTermK U (π ^ 2 * (((m₁ + i : ℕ) : ℝ) + 1 / 2) ^ 2) ≤ 2 * mBound U m₁ := by
  have hratio : ∀ m ≥ m₁, mBound U (m + 1) ≤ mBound U m / 2 := by
    intro m hm
    have hmm : (m₁ : ℝ) ≤ m := by exact_mod_cast hm
    have hsplit : rexp (-(π ^ 2 * (((m + 1 : ℕ) : ℝ) + 1 / 2) ^ 2 / U)) =
        rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / U)) * rexp (-(π ^ 2 * (2 * m + 2) / U)) := by
      rw [← exp_add]; congr 1; push_cast; field_simp; ring
    have hE' : rexp (-(π ^ 2 * (2 * m + 2) / U)) ≤ 1 / 2 := by
      refine (exp_le_exp.2 ?_).trans hE
      rw [neg_le_neg_iff]
      gcongr
    unfold mBound
    rw [hsplit]
    have h0 : 0 ≤ 2 * √(π * U) * kerG U * rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / U)) := by
      have := kerG_nonneg hU.le; positivity
    calc 2 * √(π * U) * kerG U * (rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / U)) *
          rexp (-(π ^ 2 * (2 * m + 2) / U)))
        = (2 * √(π * U) * kerG U * rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / U))) *
          rexp (-(π ^ 2 * (2 * m + 2) / U)) := by ring
      _ ≤ (2 * √(π * U) * kerG U * rexp (-(π ^ 2 * ((m : ℝ) + 1 / 2) ^ 2 / U))) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hE' h0
      _ = _ := by ring
  have h := tail_le_two_mul (fun m => mBound U m) m₁ (fun m hm => by
    rw [Real.norm_of_nonneg (mBound_nonneg hU _), Real.norm_of_nonneg (mBound_nonneg hU _)]
    exact hratio m hm)
  rw [Real.norm_of_nonneg (mBound_nonneg hU _),
    Real.norm_of_nonneg (tsum_nonneg fun i => mBound_nonneg hU _)] at h
  have hle : ∀ i, dualTermK U (π ^ 2 * (((m₁ + i : ℕ) : ℝ) + 1 / 2) ^ 2) ≤ mBound U (m₁ + i) :=
    fun i => dualTermK_le hU (by positivity)
  have hs := Summable.of_nonneg_of_le (fun i => dualTermK_nonneg) hle h.1
  exact ⟨hs, (hs.tsum_le_tsum hle h.1).trans h.2⟩

/-! ### The `k`-series -/

/-- The `n`-th term `(4/κ)^n e^{-x} e_n(x)/n²` of `I_k` (`κ = k²`, `x = κU`). -/
noncomputable def tK (κ x : ℝ) (n : ℕ) : ℝ := (4 / κ) ^ n * (rexp (-x) * eT n x) / (n : ℝ) ^ 2

/-- `τ_n = (4/κ)^n min(1, n x^{n-1} e^{-x}/(n-1)!)/n²`, written with `n = m + 1`. -/
noncomputable def tau (κ x : ℝ) (m : ℕ) : ℝ :=
  (4 / κ) ^ (m + 1) * min 1 ((m + 1) * x ^ m * rexp (-x) / (m ! : ℝ)) / ((m : ℝ) + 1) ^ 2

lemma eT_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ eT n x :=
  Finset.sum_nonneg fun j _ => by positivity

lemma exp_neg_mul_eT_le_one {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : rexp (-x) * eT n x ≤ 1 := by
  have := Real.sum_le_exp_of_nonneg hx n
  rw [exp_neg, inv_mul_le_iff₀ (exp_pos x), mul_one]; exact this

lemma pow_div_factorial_mono {x : ℝ} (hx : 0 ≤ x) {j m : ℕ} (hjm : j ≤ m) (hm : (m : ℝ) ≤ x) :
    x ^ j / (j ! : ℝ) ≤ x ^ m / (m ! : ℝ) := by
  induction m, hjm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hjm ih =>
    have hm' : (m : ℝ) ≤ x := by push_cast at hm; linarith
    refine (ih hm').trans ?_
    rw [Nat.factorial_succ, pow_succ]; push_cast
    have hf : (0 : ℝ) < (m ! : ℝ) := by positivity
    rw [div_le_div_iff₀ hf (by positivity)]
    have : x ^ m * ((m + 1) * (m ! : ℝ)) ≤ x ^ m * x * (m ! : ℝ) := by
      have hp : 0 ≤ x ^ m := pow_nonneg hx m
      nlinarith [mul_le_mul_of_nonneg_left (by push_cast at hm; linarith : ((m : ℝ) + 1) ≤ x)
        (mul_nonneg hp hf.le)]
    linarith

/-- `e_{m+1}(x) ≤ (m+1) x^m/m!` when `m ≤ x` (the terms increase). -/
lemma eT_le_last {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : (m : ℝ) ≤ x) :
    eT (m + 1) x ≤ (m + 1) * x ^ m / (m ! : ℝ) := by
  unfold eT
  calc ∑ j ∈ Finset.range (m + 1), x ^ j / (j ! : ℝ) ≤ ∑ j ∈ Finset.range (m + 1), x ^ m / (m ! : ℝ) :=
        Finset.sum_le_sum fun j hj => pow_div_factorial_mono hx (Nat.lt_succ_iff.1
          (Finset.mem_range.1 hj)) hm
    _ = _ := by simp; ring

lemma tK_nonneg {κ x : ℝ} (hκ : 0 < κ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ tK κ x n := by
  unfold tK; have := eT_nonneg hx n; positivity

lemma tK_le_geom {κ x : ℝ} (hκ : 0 < κ) (hx : 0 ≤ x) (n : ℕ) :
    tK κ x n ≤ (4 / κ) ^ n / (n : ℝ) ^ 2 := by
  unfold tK
  have h1 := exp_neg_mul_eT_le_one hx n
  have h0 : 0 ≤ (4 / κ) ^ n := by positivity
  gcongr
  calc (4 / κ) ^ n * (rexp (-x) * eT n x) ≤ (4 / κ) ^ n * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

lemma tK_le_tau {κ x : ℝ} (hκ : 0 < κ) (hx : 0 ≤ x) {m : ℕ} (hm : (m : ℝ) ≤ x) :
    tK κ x (m + 1) ≤ tau κ x m := by
  unfold tK tau
  push_cast
  have h1 := exp_neg_mul_eT_le_one hx (m + 1)
  have h2 : rexp (-x) * eT (m + 1) x ≤ (m + 1) * x ^ m * rexp (-x) / (m ! : ℝ) := by
    have := mul_le_mul_of_nonneg_left (eT_le_last hx hm) (exp_pos (-x)).le
    calc rexp (-x) * eT (m + 1) x ≤ rexp (-x) * ((m + 1) * x ^ m / (m ! : ℝ)) := this
      _ = _ := by ring
  have h0 : 0 ≤ (4 / κ) ^ (m + 1) := by positivity
  gcongr
  exact le_min h1 h2

/-- **`τ` halves**: `τ_{n+1} ≤ τ_n/2` for `κ ≥ 9`, `U ≤ ¼`, `x = κU`. -/
lemma tau_ratio {κ U : ℝ} (hκ : 9 ≤ κ) (hU0 : 0 < U) (hU : U ≤ 1 / 4) (m : ℕ) :
    tau κ (κ * U) (m + 1) ≤ tau κ (κ * U) m / 2 := by
  set x := κ * U
  have hκ0 : 0 < κ := by linarith
  have hx : 0 < x := mul_pos hκ0 hU0
  set a : ℝ := (m + 1) * x ^ m * rexp (-x) / (m ! : ℝ)
  set r : ℝ := x * (m + 2) / ((m : ℝ) + 1) ^ 2
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hnext : (((m + 1 : ℕ) : ℝ) + 1) * x ^ (m + 1) * rexp (-x) / ((m + 1)! : ℝ) = a * r := by
    simp only [a, r]
    rw [Nat.factorial_succ]; push_cast
    have hf : (m ! : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hmin : min 1 (a * r) ≤ max 1 r * min 1 a := by
    rcases le_total 1 a with h | h
    · rw [min_eq_left h, mul_one]; exact (min_le_left _ _).trans (le_max_left _ _)
    · rw [min_eq_right h]
      calc min 1 (a * r) ≤ a * r := min_le_right _ _
        _ ≤ a * max 1 r := mul_le_mul_of_nonneg_left (le_max_right _ _) ha0
        _ = _ := mul_comm _ _
  have hq1 : (4 / κ) * 1 / (((m : ℝ) + 1 + 1) ^ 2) ≤ 1 / (2 * ((m : ℝ) + 1) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 / κ ≤ 4 / 9 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hκ
    nlinarith [sq_nonneg ((m : ℝ) + 1)]
  have hq2 : (4 / κ) * r / (((m : ℝ) + 1 + 1) ^ 2) ≤ 1 / (2 * ((m : ℝ) + 1) ^ 2) := by
    simp only [r, x]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp
    nlinarith [sq_nonneg ((m : ℝ) + 1), mul_pos hU0 hm1]
  have hq : (4 / κ) * max 1 r / (((m : ℝ) + 1 + 1) ^ 2) ≤ 1 / (2 * ((m : ℝ) + 1) ^ 2) := by
    rcases le_total 1 r with h | h
    · rw [max_eq_right h]; exact hq2
    · rw [max_eq_left h]; exact hq1
  unfold tau
  rw [hnext]
  push_cast
  have hmina : 0 ≤ min 1 a := le_min zero_le_one ha0
  have hp : 0 ≤ (4 / κ) ^ (m + 1) := by positivity
  calc (4 / κ) ^ (m + 1 + 1) * min 1 (a * r) / ((m : ℝ) + 1 + 1) ^ 2
      ≤ (4 / κ) ^ (m + 1 + 1) * (max 1 r * min 1 a) / ((m : ℝ) + 1 + 1) ^ 2 := by
        gcongr
    _ = ((4 / κ) ^ (m + 1) * min 1 a) * ((4 / κ) * max 1 r / (((m : ℝ) + 1 + 1) ^ 2)) := by
        rw [pow_succ]; ring
    _ ≤ ((4 / κ) ^ (m + 1) * min 1 a) * (1 / (2 * ((m : ℝ) + 1) ^ 2)) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hp hmina)
    _ = _ := by simp only [a]; field_simp

lemma tau_nonneg {κ x : ℝ} (hκ : 0 < κ) (hx : 0 ≤ x) (m : ℕ) : 0 ≤ tau κ x m := by
  unfold tau
  have : 0 ≤ min 1 ((m + 1) * x ^ m * rexp (-x) / (m ! : ℝ)) := le_min zero_le_one (by positivity)
  positivity

lemma summable_tK {κ x : ℝ} (hκ : 9 ≤ κ) (hx : 0 ≤ x) : Summable (tK κ x) := by
  have hκ0 : 0 < κ := by linarith
  have hr : 4 / κ < 1 := by rw [div_lt_one hκ0]; linarith
  refine Summable.of_nonneg_of_le (tK_nonneg hκ0 hx) (fun n => (tK_le_geom hκ0 hx n).trans ?_)
    (summable_geometric_of_lt_one (by positivity) hr)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
    exact div_le_self (by positivity) this

/-- **Tail of the `k`-series** (Section 6.4.2): for `κ ≥ 9`, `0 < U ≤ ¼`, `x = κU`, `1 ≤ N ≤ n₁`
and `n₁ < x + 2` (e.g. `n₁ = ⌈x⌉ + 1`), `∑_{n ≥ N} t_n ≤ 2τ_N + (9/5)(4/κ)^{n₁}/n₁²`. -/
theorem kSeries_tail {κ U : ℝ} (hκ : 9 ≤ κ) (hU0 : 0 < U) (hU : U ≤ 1 / 4) {N n₁ : ℕ}
    (hN : 1 ≤ N) (hNn : N ≤ n₁) (hn₁ : (n₁ : ℝ) < κ * U + 2) :
    ∑' i, tK κ (κ * U) (N + i) ≤ 2 * tau κ (κ * U) (N - 1) +
      9 / 5 * ((4 / κ) ^ n₁ / (n₁ : ℝ) ^ 2) := by
  set x := κ * U
  have hκ0 : 0 < κ := by linarith
  have hx : 0 ≤ x := (mul_pos hκ0 hU0).le
  have hs : Summable (fun i => tK κ x (N + i)) :=
    ((summable_nat_add_iff N).2 (summable_tK hκ hx)).congr (fun i => by rw [add_comm])
  obtain ⟨d, rfl⟩ : ∃ d, n₁ = N + d := ⟨n₁ - N, by omega⟩
  rw [← hs.sum_add_tsum_nat_add d]
  -- the finite part
  have hfin : ∑ i ∈ Finset.range d, tK κ x (N + i) ≤ 2 * tau κ x (N - 1) := by
    have hτ : ∀ i, tau κ x (N - 1 + i) ≤ tau κ x (N - 1) / 2 ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [← add_assoc, pow_succ]
        calc tau κ x (N - 1 + i + 1) ≤ tau κ x (N - 1 + i) / 2 := tau_ratio hκ hU0 hU _
          _ ≤ tau κ x (N - 1) / 2 ^ i / 2 := by gcongr
          _ = _ := by rw [div_div]
    calc ∑ i ∈ Finset.range d, tK κ x (N + i)
        ≤ ∑ i ∈ Finset.range d, tau κ x (N - 1) * (1 / 2) ^ i := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have heq : N + i = (N - 1 + i) + 1 := by omega
          rw [heq]
          refine (tK_le_tau hκ0 hx ?_).trans ((hτ i).trans (le_of_eq ?_))
          · have : ((N - 1 + i : ℕ) : ℝ) + 2 ≤ ((N + d : ℕ) : ℝ) := by
              have : N - 1 + i + 2 ≤ N + d := by omega
              exact_mod_cast this
            linarith
          · rw [one_div_pow, div_eq_mul_one_div]
      _ = tau κ x (N - 1) * ∑ i ∈ Finset.range d, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ tau κ x (N - 1) * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (tau_nonneg hκ0 hx _)
          have := sum_geometric_two_le d
          simpa using this
      _ = _ := by ring
  -- the geometric tail
  have htail : ∑' i, tK κ x (N + (i + d)) ≤ 9 / 5 * ((4 / κ) ^ (N + d) / ((N + d : ℕ) : ℝ) ^ 2) := by
    set A := (4 / κ) ^ (N + d) / ((N + d : ℕ) : ℝ) ^ 2
    have hA : 0 ≤ A := by positivity
    have hle : ∀ i, tK κ x (N + (i + d)) ≤ A * (4 / 9) ^ i := by
      intro i
      refine (tK_le_geom hκ0 hx _).trans ?_
      have h1 : ((N + d : ℕ) : ℝ) ^ 2 ≤ ((N + (i + d) : ℕ) : ℝ) ^ 2 := by
        have : ((N + d : ℕ) : ℝ) ≤ ((N + (i + d) : ℕ) : ℝ) := by exact_mod_cast (by omega)
        exact pow_le_pow_left₀ (by positivity) this 2
      have h2 : (4 / κ) ^ i ≤ (4 / 9) ^ i :=
        pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hκ) i
      have hpos : (0 : ℝ) < ((N + d : ℕ) : ℝ) ^ 2 := by
        have : 1 ≤ N + d := by omega
        positivity
      rw [show N + (i + d) = (N + d) + i by ring, pow_add]
      calc (4 / κ) ^ (N + d) * (4 / κ) ^ i / ((N + d + i : ℕ) : ℝ) ^ 2
          ≤ (4 / κ) ^ (N + d) * (4 / κ) ^ i / ((N + d : ℕ) : ℝ) ^ 2 := by
            refine div_le_div_of_nonneg_left (by positivity) hpos ?_
            simpa [add_comm, add_left_comm, add_assoc] using h1
        _ ≤ (4 / κ) ^ (N + d) * (4 / 9) ^ i / ((N + d : ℕ) : ℝ) ^ 2 := by gcongr
        _ = _ := by simp only [A]; ring
    have hg : Summable fun i : ℕ => A * (4 / 9 : ℝ) ^ i :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left A
    calc ∑' i, tK κ x (N + (i + d)) ≤ ∑' i : ℕ, A * (4 / 9 : ℝ) ^ i :=
          ((summable_nat_add_iff d).2 hs).tsum_le_tsum hle hg
      _ = 9 / 5 * A := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  calc ∑ i ∈ Finset.range d, tK κ x (N + i) + ∑' i, tK κ x (N + (i + d))
      ≤ 2 * tau κ x (N - 1) + 9 / 5 * ((4 / κ) ^ (N + d) / ((N + d : ℕ) : ℝ) ^ 2) :=
        add_le_add hfin htail
    _ = _ := rfl

/-- The paper's choice `n₁ = ⌈x⌉ + 1`. -/
theorem kSeries_tail_ceil {κ U : ℝ} (hκ : 9 ≤ κ) (hU0 : 0 < U) (hU : U ≤ 1 / 4) {N : ℕ}
    (hN : 1 ≤ N) (hNn : N ≤ ⌈κ * U⌉₊ + 1) :
    ∑' i, tK κ (κ * U) (N + i) ≤ 2 * tau κ (κ * U) (N - 1) +
      9 / 5 * ((4 / κ) ^ (⌈κ * U⌉₊ + 1) / (((⌈κ * U⌉₊ + 1 : ℕ) : ℝ)) ^ 2) := by
  refine kSeries_tail hκ hU0 hU hN hNn ?_
  have := Nat.ceil_lt_add_one (mul_pos (by linarith : (0 : ℝ) < κ) hU0).le
  push_cast; linarith

/-- The terms of the closed form of `I_k` (`hasSum_kTermK`) are the `t_n`. -/
lemma kTermK_term_eq (U : ℝ) (k n : ℕ) :
    rexp (-((k : ℝ) ^ 2 * U)) * ((4 / (k : ℝ) ^ 2) ^ (n + 1) * eT (n + 1) ((k : ℝ) ^ 2 * U) /
      ((n : ℝ) + 1) ^ 2) = tK ((k : ℝ) ^ 2) ((k : ℝ) ^ 2 * U) (n + 1) := by
  unfold tK; push_cast; ring

/-- **Truncation of `I_k`**: after the first `N` terms of `I_k = ∑_{n ≥ 1} t_n` the error is
`∑_{n ≥ N+1} t_n`, bounded as in `kSeries_tail`. -/
theorem kTermK_sub_partial {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : 3 ≤ k) (N : ℕ) :
    kTermK U k - ∑ n ∈ Finset.range N, tK ((k : ℝ) ^ 2) ((k : ℝ) ^ 2 * U) (n + 1) =
      ∑' i, tK ((k : ℝ) ^ 2) ((k : ℝ) ^ 2 * U) (N + 1 + i) := by
  have hS := hasSum_kTermK hU hk
  simp_rw [kTermK_term_eq] at hS
  rw [← hS.tsum_eq, ← hS.summable.sum_add_tsum_nat_add N]
  simp only [add_sub_cancel_left]
  congr 1; ext i; congr 1; ring

/-! ### Main term and constants -/

lemma piT_nonneg {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : 0 ≤ piT n y := by
  unfold piT; linarith [exp_neg_mul_eT_le_one hy n]

/-- `π_n(y) ≤ y^n/n!` (the Poisson tail `P[Poisson(y) ≥ n]`). -/
lemma piT_le {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : piT n y ≤ y ^ n / (n ! : ℝ) := by
  have hexp : HasSum (fun j : ℕ => y ^ j / (j ! : ℝ)) (rexp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have htail : rexp y - eT n y = ∑' i, y ^ (n + i) / ((n + i)! : ℝ) := by
    rw [← hexp.tsum_eq, ← hexp.summable.sum_add_tsum_nat_add n]
    unfold eT; simp only [add_comm n, add_sub_cancel_left]
  have hle : ∀ i, y ^ (n + i) / ((n + i)! : ℝ) ≤ y ^ n / (n ! : ℝ) * (y ^ i / (i ! : ℝ)) := by
    intro i
    have h1 : ((n ! * i ! : ℕ) : ℝ) ≤ ((n + i)! : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n i)
    rw [pow_add, div_mul_div_comm]
    push_cast at h1
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  have hs : Summable fun i => y ^ (n + i) / ((n + i)! : ℝ) :=
    ((summable_nat_add_iff n).2 hexp.summable).congr (fun i => by rw [add_comm])
  have h2 : ∑' i, y ^ (n + i) / ((n + i)! : ℝ) ≤ y ^ n / (n ! : ℝ) * rexp y := by
    rw [← hexp.tsum_eq, ← tsum_mul_left]
    exact hs.tsum_le_tsum hle (hexp.summable.mul_left _)
  unfold piT
  have he := exp_pos y
  have : 1 - rexp (-y) * eT n y = rexp (-y) * (rexp y - eT n y) := by
    rw [mul_sub, ← exp_add, neg_add_cancel, exp_zero]
  rw [this, htail]
  calc rexp (-y) * ∑' i, y ^ (n + i) / ((n + i)! : ℝ) ≤ rexp (-y) * (y ^ n / (n ! : ℝ) * rexp y) :=
        mul_le_mul_of_nonneg_left h2 (exp_pos _).le
    _ = y ^ n / (n ! : ℝ) := by rw [mul_comm, mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]

/-- The `n`-th term of the closed form of `M` (`hasSum_mainK3`). -/
noncomputable def mTerm (U : ℝ) (n : ℕ) : ℝ := 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 *
    (piT (n + 1) U - (4 ^ (n + 1))⁻¹ * piT (n + 1) (4 * U)) -
    (4 * U) ^ (n + 1) / (2 * ((n : ℝ) + 1) ^ 2 * ((n + 1)! : ℝ))

/-- The majorant `(4U)^n/(n² n!)` (with `n + 1` for `n`). -/
noncomputable def mMaj (U : ℝ) (n : ℕ) : ℝ := (4 * U) ^ (n + 1) / (((n : ℝ) + 1) ^ 2 * ((n + 1)! : ℝ))

/-- **Terms of `M`**: `|M_n| ≤ (5/2)(4U)^n/(n² n!)`. -/
theorem abs_mTerm_le {U : ℝ} (hU : 0 ≤ U) (n : ℕ) : |mTerm U n| ≤ 5 / 2 * mMaj U n := by
  have h1 := piT_le hU (n + 1)
  have h2 := piT_le (by linarith : 0 ≤ 4 * U) (n + 1)
  have h1' := piT_nonneg hU (n + 1)
  have h2' := piT_nonneg (by linarith : 0 ≤ 4 * U) (n + 1)
  have hP : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 * ((n + 1)! : ℝ) := by positivity
  have h4 : (0 : ℝ) < 4 ^ (n + 1) := by positivity
  set A := 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 * piT (n + 1) U
  set B := 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 * ((4 ^ (n + 1))⁻¹ * piT (n + 1) (4 * U))
  set C := (4 * U) ^ (n + 1) / (2 * ((n : ℝ) + 1) ^ 2 * ((n + 1)! : ℝ))
  have hm : mTerm U n = A - B - C := by unfold mTerm; simp only [A, B, C]; ring
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hC0 : 0 ≤ C := by positivity
  have hA : A ≤ mMaj U n := by
    simp only [A, mMaj]
    calc 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 * piT (n + 1) U
        ≤ 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 * (U ^ (n + 1) / ((n + 1)! : ℝ)) := by gcongr
      _ = _ := by rw [mul_pow]; field_simp
  have hB : B ≤ mMaj U n := by
    simp only [B, mMaj]
    calc 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 * ((4 ^ (n + 1))⁻¹ * piT (n + 1) (4 * U))
        = piT (n + 1) (4 * U) / ((n : ℝ) + 1) ^ 2 := by field_simp
      _ ≤ (4 * U) ^ (n + 1) / ((n + 1)! : ℝ) / ((n : ℝ) + 1) ^ 2 := by gcongr
      _ = _ := by field_simp
  have hC : C = mMaj U n / 2 := by simp only [C, mMaj]; field_simp
  rw [hm, abs_le]; constructor <;> linarith

/-- **Tail of `M`**: once `4U ≤ (N+1)/2`, `∑_{n ≥ N} |M_n| ≤ 5 (4U)^{N+1}/((N+1)²(N+1)!)`. -/
theorem mTail_le' {U : ℝ} (hU : 0 < U) {N : ℕ} (hN : 4 * U ≤ ((N : ℝ) + 1) / 2) :
    Summable (fun i => mTerm U (N + i)) ∧ |∑' i, mTerm U (N + i)| ≤ 5 * mMaj U N := by
  have hMnn : ∀ n, 0 ≤ mMaj U n := fun n => by unfold mMaj; positivity
  have hratio : ∀ n ≥ N, mMaj U (n + 1) ≤ mMaj U n / 2 := by
    intro n hn
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hf : (0 : ℝ) < ((n + 1)! : ℝ) := by positivity
    have hsplit : mMaj U (n + 1) = mMaj U n * (4 * U * ((n : ℝ) + 1) ^ 2 /
        (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 2))) := by
      unfold mMaj
      rw [Nat.factorial_succ (n + 1), pow_succ]; push_cast
      field_simp; ring
    have hq : 4 * U * ((n : ℝ) + 1) ^ 2 / (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 2)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 4 * U ≤ ((n : ℝ) + 1) / 2 := hN.trans (by linarith)
      have h2 : 0 ≤ ((n : ℝ) + 1) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    rw [hsplit]
    calc mMaj U n * (4 * U * ((n : ℝ) + 1) ^ 2 / (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 2)))
        ≤ mMaj U n * (1 / 2) := mul_le_mul_of_nonneg_left hq (hMnn n)
      _ = _ := by ring
  have h := tail_le_two_mul (fun n => mMaj U n) N (fun n hn => by
    rw [Real.norm_of_nonneg (hMnn _), Real.norm_of_nonneg (hMnn _)]; exact hratio n hn)
  rw [Real.norm_of_nonneg (hMnn _), Real.norm_of_nonneg (tsum_nonneg fun i => hMnn _)] at h
  have hle : ∀ i, ‖mTerm U (N + i)‖ ≤ 5 / 2 * mMaj U (N + i) := fun i => by
    rw [Real.norm_eq_abs]; exact abs_mTerm_le hU.le _
  have hs : Summable (fun i => mTerm U (N + i)) :=
    Summable.of_norm_bounded (h.1.mul_left (5 / 2)) hle
  refine ⟨hs, ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖∑' i, mTerm U (N + i)‖ ≤ ∑' i, 5 / 2 * mMaj U (N + i) :=
        tsum_of_norm_bounded (h.1.mul_left (5 / 2)).hasSum hle
    _ = 5 / 2 * ∑' i, mMaj U (N + i) := tsum_mul_left
    _ ≤ 5 / 2 * (2 * mMaj U N) := by gcongr; exact h.2
    _ = _ := by ring

/-- `(5/2)(4U)^n/(n² n!) ≤ 3(8U)^n/n!`: the paper's form of the bound on the terms of `M`. -/
lemma mMaj_le_paper {U : ℝ} (hU : 0 ≤ U) (n : ℕ) :
    5 / 2 * mMaj U n ≤ 3 * (8 * U) ^ (n + 1) / ((n + 1)! : ℝ) := by
  have hf : (0 : ℝ) < ((n + 1)! : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 : (4 * U) ^ (n + 1) ≤ (8 * U) ^ (n + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hA : 0 ≤ (4 * U) ^ (n + 1) := by positivity
  have e1 : (4 * U) ^ (n + 1) / (((n : ℝ) + 1) ^ 2 * ((n + 1)! : ℝ)) ≤
      (4 * U) ^ (n + 1) / ((n + 1)! : ℝ) :=
    div_le_div_of_nonneg_left hA hf (le_mul_of_one_le_left hf.le h1)
  have e2 : (4 * U) ^ (n + 1) / ((n + 1)! : ℝ) ≤ (8 * U) ^ (n + 1) / ((n + 1)! : ℝ) :=
    div_le_div_of_nonneg_right h2 hf.le
  have key : mMaj U n ≤ (8 * U) ^ (n + 1) / ((n + 1)! : ℝ) := by unfold mMaj; exact e1.trans e2
  have e3 : 0 ≤ (8 * U) ^ (n + 1) / ((n + 1)! : ℝ) := by positivity
  calc 5 / 2 * mMaj U n ≤ 3 * ((8 * U) ^ (n + 1) / ((n + 1)! : ℝ)) := by linarith
    _ = _ := by ring

/-- **The constant `Li₂(1/9)`**: the tail of `∑ 9^{-n}/n²` after `N` terms is at most `9^{-N}`. -/
theorem Li₂_ninth_tail (N : ℕ) :
    |Li₂ (1 / 9) - ∑ n ∈ Finset.range N, (1 / 9 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 2| ≤
      (1 / 9 : ℝ) ^ N := by
  have hS := hasSum_Li₂ (x := 1 / 9) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [← hS.tsum_eq, ← hS.summable.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hs := (summable_nat_add_iff N).2 hS.summable
  have hnn : ∀ i, 0 ≤ (1 / 9 : ℝ) ^ (i + N + 1) / (((i + N : ℕ) : ℝ) + 1) ^ 2 :=
    fun i => by positivity
  rw [abs_of_nonneg (tsum_nonneg hnn)]
  have hle : ∀ i, (1 / 9 : ℝ) ^ (i + N + 1) / (((i + N : ℕ) : ℝ) + 1) ^ 2 ≤
      (1 / 9 : ℝ) ^ (N + 1) * (1 / 9) ^ i := by
    intro i
    have h1 : (1 : ℝ) ≤ (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
      nlinarith [((i + N : ℕ).cast_nonneg : (0 : ℝ) ≤ (i + N : ℕ))]
    refine (div_le_self (by positivity) h1).trans (le_of_eq ?_)
    rw [← pow_add]; congr 1; ring
  have hg : Summable fun i : ℕ => (1 / 9 : ℝ) ^ (N + 1) * (1 / 9) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∑' i, (1 / 9 : ℝ) ^ (i + N + 1) / (((i + N : ℕ) : ℝ) + 1) ^ 2
      ≤ ∑' i : ℕ, (1 / 9 : ℝ) ^ (N + 1) * (1 / 9) ^ i := hs.tsum_le_tsum hle hg
    _ = (1 / 9 : ℝ) ^ N / 8 := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]; ring
    _ ≤ _ := by have : (0 : ℝ) ≤ (1 / 9) ^ N := by positivity
                linarith

end ZetaF.K3Bounds
