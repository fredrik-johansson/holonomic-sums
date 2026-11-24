/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Closed forms of `I_k` and `M` in Theorem 6.3

With `e_n(y) = ∑_{j<n} y^j/j!` and `π_n(y) = 1 - e^{-y} e_n(y)`,
* `I_k = ∫_U^∞ e^{-k²u} G(u) du = e^{-k²U} ∑_{n≥1} (4/k²)^n e_n(k²U)/n²` (`k ≥ 3`);
* `M = ∫_0^U (e^{-u} - e^{-4u} - ½) G(u) du
     = ∑_{n≥1} 4^n/n² (π_n(U) - 4^{-n} π_n(4U)) - ½ ∑_{n≥1} (4U)^n/(n² n!)`.
* `J_m = √π ∑_{n≥1} 4^n/(n·n!) D_{n-1/2}(c_m)
       = √π (D_{-1/2} ∑_{n≥1} (-16c)^n/(n(2n)!) + E ∑_{n≥1} 4^n/(n·n!) β_n)`, with `D_a`, `α_n`, `β_n`
  as in `ZetaF.Khinchin.StartVals` (the remaining identifications `D_{-1/2} = √(π/c) erfc √(c/U)` and
  `∑ (-16c)^n/(n(2n)!) = 2(Ci(4√c) - γ - log(4√c))` are not formalized).
The first two follow termwise from the incomplete-gamma integrals
`∫_U^∞ e^{-κu} u^n du = n!/κ^{n+1} e^{-κU} e_{n+1}(κU)` and
`∫_0^U e^{-au} u^n du = n!/a^{n+1} π_{n+1}(aU)`.
-/
import ZetaF.Khinchin.K3Split
import ZetaF.Khinchin.StartVals

open MeasureTheory Set Filter Real
open scoped Nat Topology

namespace ZetaF.K3Closed

/-- The truncated exponential `e_n(y) = ∑_{j<n} y^j/j!`. -/
noncomputable def eT (n : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range n, y ^ j / (j ! : ℝ)

/-- `π_n(y) = 1 - e^{-y} e_n(y)`. -/
noncomputable def piT (n : ℕ) (y : ℝ) : ℝ := 1 - rexp (-y) * eT n y

lemma eT_zero_arg (n : ℕ) : eT (n + 1) 0 = 1 := by
  simp [eT, Finset.sum_range_succ']

lemma hasDerivAt_exp_eT (κ : ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u => rexp (-(κ * u)) * eT (n + 1) (κ * u))
      (-(κ * rexp (-(κ * u)) * (κ * u) ^ n / (n ! : ℝ))) u := by
  have hE : HasDerivAt (fun u => rexp (-(κ * u))) (-(κ * rexp (-(κ * u)))) u := by
    have h0 : HasDerivAt (fun u => -(κ * u)) (-κ) u := by
      have := ((hasDerivAt_id' u).const_mul κ).neg; rwa [mul_one] at this
    convert h0.exp using 1; ring
  induction n with
  | zero =>
    have : (fun u => rexp (-(κ * u)) * eT (0 + 1) (κ * u)) = fun u => rexp (-(κ * u)) := by
      ext v; simp [eT]
    rw [this]; convert hE using 1; simp
  | succ n ih =>
    have hsplit : (fun u => rexp (-(κ * u)) * eT (n + 1 + 1) (κ * u)) = fun u =>
        rexp (-(κ * u)) * eT (n + 1) (κ * u) +
          rexp (-(κ * u)) * ((κ * u) ^ (n + 1) / ((n + 1)! : ℝ)) := by
      ext v; simp only [eT]; rw [Finset.sum_range_succ (n := n + 1)]; ring
    rw [hsplit]
    have hP : HasDerivAt (fun u => (κ * u) ^ (n + 1) / ((n + 1)! : ℝ))
        ((n + 1 : ℕ) * (κ * u) ^ n * κ / ((n + 1)! : ℝ)) u := by
      have h0 : HasDerivAt (fun u => κ * u) κ u := by
        have := (hasDerivAt_id' u).const_mul κ; rwa [mul_one] at this
      have := (h0.pow (n + 1)).div_const ((n + 1)! : ℝ)
      convert this using 1; simp
    convert ih.add (hE.mul hP) using 1
    have hf : ((n ! : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.factorial_succ]; push_cast
    field_simp
    ring

/-- The antiderivative `-(n!/κ^{n+1}) e^{-κu} e_{n+1}(κu)` of `e^{-κu} u^n`. -/
lemma hasDerivAt_antideriv {κ : ℝ} (hκ : κ ≠ 0) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u => -((n ! : ℝ) / κ ^ (n + 1)) * (rexp (-(κ * u)) * eT (n + 1) (κ * u)))
      (rexp (-(κ * u)) * u ^ n) u := by
  convert (hasDerivAt_exp_eT κ n u).const_mul (-((n ! : ℝ) / κ ^ (n + 1))) using 1
  have hf : (n ! : ℝ) ≠ 0 := by positivity
  rw [mul_pow]; field_simp; ring

lemma integrableOn_exp_pow {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    IntegrableOn (fun u => rexp (-(κ * u)) * u ^ n) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := κ)
    (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by norm_num) hκ
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]; ring

lemma tendsto_exp_eT {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    Tendsto (fun u => rexp (-(κ * u)) * eT (n + 1) (κ * u)) atTop (𝓝 0) := by
  have h : ∀ j ∈ Finset.range (n + 1), Tendsto (fun u => (κ * u) ^ j * rexp (-(κ * u)) /
      (j ! : ℝ)) atTop (𝓝 0) := by
    intro j _
    have := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
      (tendsto_id.const_mul_atTop hκ)).div_const (j ! : ℝ)
    simpa using this
  have := tendsto_finsetSum _ h
  simp only [Finset.sum_const_zero] at this
  refine this.congr (fun u => ?_)
  simp only [eT, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_); ring

/-- **`∫_U^∞ e^{-κu} u^n du = n!/κ^{n+1} e^{-κU} e_{n+1}(κU)`.** -/
theorem integral_Ioi_exp_pow {κ U : ℝ} (hκ : 0 < κ) (hU : 0 ≤ U) (n : ℕ) :
    ∫ u in Ioi U, rexp (-(κ * u)) * u ^ n =
      (n ! : ℝ) / κ ^ (n + 1) * rexp (-(κ * U)) * eT (n + 1) (κ * U) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hasDerivAt_antideriv hκ.ne' n u)
    ((integrableOn_exp_pow hκ n).mono_set (Ioi_subset_Ioi hU))
    (by simpa using (tendsto_exp_eT hκ n).const_mul (-((n ! : ℝ) / κ ^ (n + 1))))]
  ring

/-- **`∫_0^U e^{-au} u^n du = n!/a^{n+1} π_{n+1}(aU)`.** -/
theorem integral_Ioc_exp_pow {a U : ℝ} (ha : 0 < a) (hU : 0 ≤ U) (n : ℕ) :
    ∫ u in (0 : ℝ)..U, rexp (-(a * u)) * u ^ n = (n ! : ℝ) / a ^ (n + 1) * piT (n + 1) (a * U) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_antideriv ha.ne' n u)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, eT_zero_arg, piT]
  ring

/-! ### `I_k` -/

/-- The coefficients `g_n = 4^{n+1}/((n+1)(n+1)!)` of `G(u) = ∑ g_n u^n`. -/
noncomputable def gK (n : ℕ) : ℝ := 4 ^ (n + 1) / ((n + 1) * ((n + 1)! : ℝ))

lemma gK_mul_factorial (n : ℕ) : gK n * (n ! : ℝ) = 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
  unfold gK
  have hf : (n ! : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]; push_cast; field_simp

lemma kerG_term_eq (n : ℕ) (u : ℝ) :
    4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ)) = gK n * u ^ n := by
  unfold gK; ring

/-- **Closed form of `I_k`**: for `k ≥ 3` and `U > 0`,
`I_k = ∑_{n ≥ 0} e^{-k²U} (4/k²)^{n+1} e_{n+1}(k²U)/(n+1)²`. -/
theorem hasSum_kTermK {U : ℝ} (hU : 0 < U) {k : ℕ} (hk : 3 ≤ k) :
    HasSum (fun n : ℕ => rexp (-((k : ℝ) ^ 2 * U)) *
      ((4 / (k : ℝ) ^ 2) ^ (n + 1) * eT (n + 1) ((k : ℝ) ^ 2 * U) / ((n : ℝ) + 1) ^ 2))
      (kTermK U k) := by
  set κ : ℝ := (k : ℝ) ^ 2
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hκ4 : 4 ≤ κ := by simp only [κ]; nlinarith
  have hκ : 0 < κ := by linarith
  set F : ℕ → ℝ → ℝ := fun n u => rexp (-(κ * u)) * (4 ^ (n + 1) * u ^ n /
    ((n + 1) * ((n + 1)! : ℝ)))
  have hint0 : ∀ n, IntegrableOn (F n) (Ioi 0) := by
    intro n
    have h : IntegrableOn (fun u => gK n * (rexp (-(κ * u)) * u ^ n)) (Ioi 0) :=
      (integrableOn_exp_pow hκ n).const_mul (gK n)
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [F, kerG_term_eq]; ring
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi U)) :=
    fun n => (hint0 n).mono_set (Ioi_subset_Ioi hU.le)
  have hFnn : ∀ n, ∀ u ∈ Ioi (0 : ℝ), 0 ≤ F n u := fun n u hu => by
    have hu : (0 : ℝ) < u := hu
    simp only [F]; positivity
  have hnorm : Summable fun n => ∫ u in Ioi U, ‖F n u‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _))
      (fun n => ?_) (laplace_kerG hκ4).1.summable
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu =>
      Real.norm_of_nonneg (hFnn n u (lt_trans hU hu)))]
    exact setIntegral_mono_set (hint0 n) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall (hFnn n))) (Eventually.of_forall (Ioi_subset_Ioi hU.le))
  have hS := hasSum_integral_of_summable_integral_norm hint hnorm
  have hlim : ∫ u in Ioi U, ∑' n, F n u = kTermK U k := by
    unfold kTermK
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [F, kerG]; rw [tsum_mul_left]
  rw [hlim] at hS
  convert hS using 1
  ext n
  have : ∫ u in Ioi U, F n u = gK n * ∫ u in Ioi U, rexp (-(κ * u)) * u ^ n := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [F, kerG_term_eq]; ring
  rw [this, integral_Ioi_exp_pow hκ hU.le n]
  have h1 := gK_mul_factorial n
  have hκn : κ ^ (n + 1) ≠ 0 := pow_ne_zero _ hκ.ne'
  rw [div_pow]
  calc rexp (-(κ * U)) * (4 ^ (n + 1) / κ ^ (n + 1) * eT (n + 1) (κ * U) / ((n : ℝ) + 1) ^ 2)
      = (4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2) / κ ^ (n + 1) * rexp (-(κ * U)) * eT (n + 1) (κ * U) := by
        ring
    _ = _ := by rw [← h1]; ring

/-! ### `M` -/

lemma abs_mainK3_weight_le {u : ℝ} (hu : 0 ≤ u) :
    |rexp (-u) - rexp (-(4 * u)) - 1 / 2| ≤ 3 / 2 := by
  have h1 : rexp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : rexp (-(4 * u)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 := Real.exp_pos (-u)
  have h4 := Real.exp_pos (-(4 * u))
  rw [abs_le]; constructor <;> linarith

/-- **Closed form of `M`**: for `U > 0`,
`M = ∑_{n ≥ 0} [4^{n+1}/(n+1)² (π_{n+1}(U) - 4^{-(n+1)} π_{n+1}(4U)) - (4U)^{n+1}/(2(n+1)²(n+1)!)]`. -/
theorem hasSum_mainK3 {U : ℝ} (hU : 0 < U) :
    HasSum (fun n : ℕ => 4 ^ (n + 1) / ((n : ℝ) + 1) ^ 2 *
        (piT (n + 1) U - (4 ^ (n + 1))⁻¹ * piT (n + 1) (4 * U)) -
        (4 * U) ^ (n + 1) / (2 * ((n : ℝ) + 1) ^ 2 * ((n + 1)! : ℝ)))
      (mainK3 U) := by
  set w : ℝ → ℝ := fun u => rexp (-u) - rexp (-(4 * u)) - 1 / 2
  set F : ℕ → ℝ → ℝ := fun n u => w u * (4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ)))
  have hcont : ∀ n, Continuous (F n) := fun n => by simp only [F, w]; fun_prop
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc 0 U)) :=
    fun n => (hcont n).integrableOn_Ioc
  have hbound : ∀ n, ∫ u in Ioc 0 U, ‖F n u‖ ≤ 3 / 2 * (4 * ((4 * U) ^ n / (n ! : ℝ))) * U := by
    intro n
    have hle : ∀ u ∈ Ioc (0 : ℝ) U, ‖F n u‖ ≤ 3 / 2 * (4 * ((4 * U) ^ n / (n ! : ℝ))) := by
      intro u hu
      have hu0 := hu.1
      have ht : 0 ≤ 4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ)) := by positivity
      simp only [F, w]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht]
      refine mul_le_mul (abs_mainK3_weight_le hu.1.le) ?_ (by have := hu.1; positivity)
        (by norm_num)
      refine (kerG_term_le hu.1.le n).trans ?_
      gcongr; exact hu.2
    calc ∫ u in Ioc 0 U, ‖F n u‖ ≤ ∫ u in Ioc 0 U, 3 / 2 * (4 * ((4 * U) ^ n / (n ! : ℝ))) :=
          setIntegral_mono_on (hint n).norm (integrableOn_const (by simp)) measurableSet_Ioc hle
      _ = _ := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hU.le, smul_eq_mul, sub_zero, mul_comm]
  have hnorm : Summable fun n => ∫ u in Ioc 0 U, ‖F n u‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _)) hbound
      ((((Real.summable_pow_div_factorial (4 * U)).mul_left 4).mul_left (3 / 2)).mul_right U)
  have hS := hasSum_integral_of_summable_integral_norm hint hnorm
  have hlim : ∫ u in Ioc 0 U, ∑' n, F n u = mainK3 U := by
    unfold mainK3
    refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    simp only [F, kerG]; rw [tsum_mul_left]
  rw [hlim] at hS
  convert hS using 1
  ext n
  rw [← intervalIntegral.integral_of_le hU.le]
  have hsplit : ∀ u, F n u = gK n * (rexp (-(1 * u)) * u ^ n) - gK n * (rexp (-(4 * u)) * u ^ n)
      - gK n / 2 * u ^ n := by
    intro u; simp only [F, w, kerG_term_eq, one_mul]; ring
  simp_rw [hsplit]
  have i1 : IntervalIntegrable (fun u : ℝ => gK n * (rexp (-(1 * u)) * u ^ n)) volume 0 U := by
    apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun u : ℝ => gK n * (rexp (-(4 * u)) * u ^ n)) volume 0 U := by
    apply Continuous.intervalIntegrable; fun_prop
  have i3 : IntervalIntegrable (fun u : ℝ => gK n / 2 * u ^ n) volume 0 U := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_Ioc_exp_pow one_pos hU.le,
    integral_Ioc_exp_pow (by norm_num) hU.le, integral_pow, one_mul, one_pow, div_one]
  have h1 := gK_mul_factorial n
  have hf : ((n + 1)! : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hfn : (n ! : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  unfold gK at h1 ⊢
  rw [hf] at h1 ⊢
  push_cast
  rw [mul_pow]
  field_simp
  ring

/-! ### `J_m` -/

open ZetaF.StartVals in
/-- **Series form of `J_m`**: `J = √π ∑_{n ≥ 0} g_n D_{n+1/2}(c)` for `c, U > 0`. -/
theorem hasSum_dualTermK {U c : ℝ} (hU : 0 < U) (hc : 0 < c) :
    HasSum (fun n : ℕ => √π * (gK n * Dint c U (((n + 1 : ℕ) : ℝ) - 1 / 2))) (dualTermK U c) := by
  set F : ℕ → ℝ → ℝ := fun n u => u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) *
    (4 ^ (n + 1) * u ^ n / ((n + 1) * ((n + 1)! : ℝ)))
  have hFk : ∀ n, ∀ u ∈ Ioc (0 : ℝ) U, F n u = gK n * kx c (((n + 1 : ℕ) : ℝ) - 1 / 2 - 1) u := by
    intro n u hu
    rw [kx_of_pos hu.1, show (((n + 1 : ℕ) : ℝ) - 1 / 2 - 1) = -(1 / 2) + (n : ℕ) by push_cast; ring,
      rpow_add hu.1, rpow_natCast]
    simp only [F, kerG_term_eq]; ring
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc 0 U)) := by
    intro n
    have h := ((intervalIntegrable_kx hc (((n + 1 : ℕ) : ℝ) - 1 / 2 - 1) hU.le).const_mul
      (gK n)).def'
    rw [uIoc_of_le hU.le] at h
    exact h.congr_fun (fun u hu => (hFk n u hu).symm) measurableSet_Ioc
  have hD : ∀ n, ∫ u in Ioc 0 U, F n u = gK n * Dint c U (((n + 1 : ℕ) : ℝ) - 1 / 2) := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioc (hFk n), integral_const_mul, Dint,
      intervalIntegral.integral_of_le hU.le]
  have hFnn : ∀ n, ∀ u ∈ Ioc (0 : ℝ) U, 0 ≤ F n u := fun n u hu => by
    have := hu.1; simp only [F]; positivity
  have hgnn : ∀ n, 0 ≤ gK n := fun n => by unfold gK; positivity
  have hnorm : Summable fun n => ∫ u in Ioc 0 U, ‖F n u‖ := by
    have hmaj : Summable fun n : ℕ => rexp (-(c / U)) * (4 * (4 ^ n / (n ! : ℝ)) *
        (U ^ ((n : ℝ) + 1 / 2) / (1 / 2))) := by
      have := (Real.summable_pow_div_factorial (4 * U)).mul_left (4 * U ^ (1 / 2 : ℝ) / (1 / 2))
      refine (this.mul_left (rexp (-(c / U)))).congr (fun n => ?_)
      rw [rpow_add hU, rpow_natCast, mul_pow]; ring
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _))
      (fun n => ?_) hmaj
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu => Real.norm_of_nonneg (hFnn n u hu)),
      hD n]
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) - 1 / 2 := by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have hDle := Dint_le hc hU hn
    have hg : gK n ≤ 4 * (4 ^ n / (n ! : ℝ)) := by
      have := kerG_term_le (u := 1) zero_le_one n
      rw [kerG_term_eq, one_pow, mul_one, mul_one] at this; exact this
    have hexp : ((n + 1 : ℕ) : ℝ) - 1 / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
    rw [hexp] at hDle
    have hDnn := (Dint_pos hc hU (((n + 1 : ℕ) : ℝ) - 1 / 2)).le
    calc gK n * Dint c U (((n + 1 : ℕ) : ℝ) - 1 / 2)
        ≤ 4 * (4 ^ n / (n ! : ℝ)) * (rexp (-(c / U)) * U ^ ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1 / 2)) := by
          rw [hexp] at hDnn ⊢
          exact mul_le_mul hg hDle hDnn (by positivity)
      _ ≤ 4 * (4 ^ n / (n ! : ℝ)) * (rexp (-(c / U)) * U ^ ((n : ℝ) + 1 / 2) / (1 / 2)) := by
          gcongr; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
      _ = _ := by ring
  have hS := hasSum_integral_of_summable_integral_norm hint hnorm
  have hlim : ∫ u in Ioc 0 U, ∑' n, F n u = ∫ u in Ioc 0 U,
      u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) * kerG u := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    simp only [F, kerG]; rw [tsum_mul_left]
  rw [hlim] at hS
  unfold dualTermK
  have := hS.mul_left √π
  simp only [hD] at this
  exact this

lemma gK_mul_alphaS (c : ℝ) (n : ℕ) :
    gK n * StartVals.alphaS c (n + 1) =
      (-16 * c) ^ (n + 1) / (((n : ℝ) + 1) * ((2 * (n + 1))! : ℝ)) := by
  unfold gK StartVals.alphaS
  have hf : ((n + 1)! : ℝ) ≠ 0 := by positivity
  have hf2 : ((2 * (n + 1))! : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  rw [← mul_pow]; congr 1; ring

lemma summable_gK_mul_alphaS (c : ℝ) : Summable fun n => gK n * StartVals.alphaS c (n + 1) := by
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial (16 * |c|)).comp_injective
    (add_left_injective 1)) (fun n => ?_)
  rw [gK_mul_alphaS, Real.norm_eq_abs, abs_div, abs_pow, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * ((2 * (n + 1))! : ℝ))]
  simp only [Function.comp, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  have h1 : ((n + 1)! : ℝ) ≤ ((n : ℝ) + 1) * ((2 * (n + 1))! : ℝ) := by
    have : ((n + 1)! : ℝ) ≤ ((2 * (n + 1))! : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n), (by positivity : (0 : ℝ) ≤ ((2 * (n + 1))! : ℝ))]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1

open ZetaF.StartVals in
/-- **`J_m` through `D_{-1/2}` and `𝓑`**: for `c, U > 0`,
`J = √π (D_{-1/2} ∑_{n≥1} (-16c)^n/(n(2n)!) + e^{-c/U} ∑_{n≥1} 4^n/(n·n!) β_n)`. -/
theorem dualTermK_eq {U c : ℝ} (hU : 0 < U) (hc : 0 < c) :
    Summable (fun n : ℕ => gK n * betaS c U (n + 1)) ∧
    dualTermK U c = √π * (Dint c U (-(1 / 2)) *
        ∑' n : ℕ, (-16 * c) ^ (n + 1) / (((n : ℝ) + 1) * ((2 * (n + 1))! : ℝ)) +
      rexp (-(c / U)) * ∑' n : ℕ, gK n * betaS c U (n + 1)) := by
  set E := rexp (-(c / U))
  set D0 := Dint c U (-(1 / 2))
  have hS := hasSum_dualTermK hU hc
  have hE : E ≠ 0 := (exp_pos _).ne'
  have hsplit : ∀ n : ℕ, gK n * Dint c U (((n + 1 : ℕ) : ℝ) - 1 / 2) =
      D0 * (gK n * alphaS c (n + 1)) + E * (gK n * betaS c U (n + 1)) := by
    intro n; rw [Dint_half_eq hc hU]; ring
  have hD : Summable fun n : ℕ => gK n * Dint c U (((n + 1 : ℕ) : ℝ) - 1 / 2) := by
    have := (hS.summable.mul_left (√π)⁻¹)
    refine this.congr (fun n => ?_)
    have : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp
  have ha := (summable_gK_mul_alphaS c).mul_left D0
  have hb : Summable fun n : ℕ => gK n * betaS c U (n + 1) := by
    have := (hD.sub ha).mul_left E⁻¹
    refine this.congr (fun n => ?_)
    rw [hsplit]; field_simp; ring
  refine ⟨hb, ?_⟩
  rw [← hS.tsum_eq, tsum_mul_left]
  simp_rw [hsplit]
  rw [ha.tsum_add (hb.mul_left E), tsum_mul_left, tsum_mul_left]
  simp_rw [gK_mul_alphaS]

end ZetaF.K3Closed
