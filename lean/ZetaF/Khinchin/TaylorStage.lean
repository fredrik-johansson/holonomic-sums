/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Taylor stages of the bit-burst evaluation (Section 6.4.2)

The state components of the dual system of Algorithm K3 are moments
`Z_t[g](c) = ∫_0^U u^{-t} e^{-c/u} g(u) du` with `t ∈ {1/2, 3/2}` and `|g| ≤ e^{4U}`
(`g = Ein⁺(4u)`, `e^{4u}` or `1`). This file proves

* the Taylor expansion `Z_t[g](c₀ + δ) = ∑_l (-δ)^l/l! Z_{t+l}[g](c₀)` for `|δ| < c₀`
  (termwise integration of `e^{-δ/u}`);
* `∫_0^∞ u^{-a} e^{-c/u} du = Γ(a-1)/c^{a-1}` (`a > 1`) and, on `(0, U]`, the refinement
  `∫_0^U u^{-a} e^{-c/u} ≤ U^j Γ(a+j-1)/c^{a+j-1}`;
* the remainder bound: after `L ≥ 2` terms the error is at most `B U^j c₀^{1-t-j} ρ^L/(1-ρ)`,
  `ρ = |δ|/c₀`, whenever `|g| ≤ B` and `1 ≤ t + j ≤ 2`. With `j = 0` for `t = 3/2` and `j = 1` for
  `t = 1/2` this gives the paper's bound `2e^{4U} ρ^L/(c₀^{1/2}(1-ρ))` for `U ≤ 2`.
-/
import ZetaF.Khinchin.StartVals

open MeasureTheory Set Filter Real
open scoped Nat Topology

namespace ZetaF.TaylorStage

open ZetaF.StartVals

/-- The real dual moment `Z_t[g](c) = ∫_0^U u^{-t} e^{-c/u} g(u) du`. -/
noncomputable def Zr (U c t : ℝ) (g : ℝ → ℝ) : ℝ := ∫ u in Ioc 0 U, kx c (-t) u * g u

/-! ### The Gamma integral -/

lemma integrableOn_kx_Ioi {c a : ℝ} (hc : 0 < c) (ha : 1 < a) : IntegrableOn (kx c (-a)) (Ioi 0) := by
  have hf : IntegrableOn (fun y : ℝ => y ^ (a - 2) * rexp (-c * y ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) (by norm_num) hc
  rw [← integrableOn_Ioi_comp_rpow_iff' _ (by norm_num : (-1 : ℝ) ≠ 0)] at hf
  refine hf.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx : 0 < x := hx
  dsimp only
  rw [kx_of_pos hx, smul_eq_mul, rpow_one, rpow_neg_one, inv_rpow hx.le, ← rpow_neg hx.le,
    ← mul_assoc, ← rpow_add hx]
  congr 1
  all_goals (try ring_nf)
  all_goals (try (congr 1; field_simp))

/-- **`∫_0^∞ u^{-a} e^{-c/u} du = Γ(a-1)/c^{a-1}`** for `a > 1`, `c > 0`. -/
theorem integral_kx_Ioi {c a : ℝ} (hc : 0 < c) (ha : 1 < a) :
    ∫ u in Ioi 0, kx c (-a) u = Real.Gamma (a - 1) / c ^ (a - 1) := by
  have h := integral_comp_rpow_Ioi (fun y : ℝ => y ^ (a - 1 - 1) * rexp (-(c * y)))
    (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hc] at h
  rw [div_eq_mul_inv, mul_comm, ← inv_rpow hc.le, ← one_div, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx : 0 < x := hx
  rw [kx_of_pos hx, smul_eq_mul, abs_neg, abs_one, one_mul, rpow_neg_one, inv_rpow hx.le,
    ← rpow_neg hx.le, ← mul_assoc, ← rpow_add hx]
  congr 1
  all_goals (try ring_nf)
  all_goals (try (congr 1; field_simp))

lemma integrableOn_kx_Ioc {c : ℝ} (hc : 0 < c) (b : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    IntegrableOn (kx c b) (Ioc 0 U) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hU).1 (intervalIntegrable_kx hc b hU)

/-- **`∫_0^U u^{-a} e^{-c/u} du ≤ U^j Γ(a+j-1)/c^{a+j-1}`** for `a + j > 1`. -/
theorem integral_kx_Ioc_le {c a U : ℝ} (hc : 0 < c) (hU : 0 < U) (j : ℕ) (ha : 1 < a + j) :
    ∫ u in Ioc 0 U, kx c (-a) u ≤ U ^ j * (Real.Gamma (a + j - 1) / c ^ (a + j - 1)) := by
  have hle : ∫ u in Ioc 0 U, kx c (-a) u ≤ ∫ u in Ioc 0 U, U ^ j * kx c (-(a + j)) u := by
    refine setIntegral_mono_on (integrableOn_kx_Ioc hc _ hU.le)
      ((integrableOn_kx_Ioc hc _ hU.le).const_mul _) measurableSet_Ioc (fun u hu => ?_)
    rw [kx_of_pos hu.1, kx_of_pos hu.1, neg_add, rpow_add hu.1, rpow_neg hu.1.le (j : ℝ),
      rpow_natCast]
    have hp : 0 < u ^ j := pow_pos hu.1 j
    have hUj : u ^ j ≤ U ^ j := pow_le_pow_left₀ hu.1.le hu.2 j
    have h0 : 0 ≤ u ^ (-a) * rexp (-(c / u)) := mul_nonneg (rpow_nonneg hu.1.le _) (exp_pos _).le
    calc u ^ (-a) * rexp (-(c / u)) = u ^ j * (u ^ (-a) * ((u ^ j)⁻¹ * rexp (-(c / u)))) := by
          field_simp
      _ ≤ U ^ j * (u ^ (-a) * ((u ^ j)⁻¹ * rexp (-(c / u)))) := by
          gcongr
          exact mul_nonneg (rpow_nonneg hu.1.le _) (mul_nonneg (inv_nonneg.2 hp.le) (exp_pos _).le)
      _ = _ := by ring
  refine hle.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hU.le j)
  rw [← integral_kx_Ioi hc ha]
  exact setIntegral_mono_set (integrableOn_kx_Ioi hc ha)
    (Eventually.of_forall fun u => kx_nonneg _ _ _) (Eventually.of_forall Ioc_subset_Ioi_self)

/-! ### The Taylor expansion -/

section Taylor

variable {U c₀ δ t B : ℝ} {g : ℝ → ℝ}

/-- The `l`-th term of the Taylor expansion, as a function of `u`. -/
noncomputable def termF (c₀ δ t : ℝ) (g : ℝ → ℝ) (l : ℕ) (u : ℝ) : ℝ :=
  (-δ) ^ l / (l ! : ℝ) * (kx c₀ (-(t + l)) u * g u)

lemma kx_add_nat {c b u : ℝ} (hu : 0 < u) (l : ℕ) :
    kx c (-(b + l)) u = kx c (-b) u * (u⁻¹) ^ l := by
  rw [kx_of_pos hu, kx_of_pos hu, neg_add, rpow_add hu, rpow_neg hu.le (l : ℝ), rpow_natCast,
    inv_pow]
  ring

lemma hasSum_termF {u : ℝ} (hu : 0 < u) :
    HasSum (fun l => termF c₀ δ t g l u) (kx (c₀ + δ) (-t) u * g u) := by
  have hexp : HasSum (fun l : ℕ => (-δ / u) ^ l / (l ! : ℝ)) (rexp (-δ / u)) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have := hexp.mul_left (kx c₀ (-t) u * g u)
  convert this using 1
  · ext l; unfold termF; rw [kx_add_nat hu, div_pow]; simp only [div_eq_mul_inv, inv_pow]; ring
  · rw [kx_of_pos hu, kx_of_pos hu, show -((c₀ + δ) / u) = -(c₀ / u) + -δ / u by ring, exp_add]
    ring

variable (hc₀ : 0 < c₀) (hδ : |δ| < c₀) (hU : 0 < U) (hg : ContinuousOn g (Ioc 0 U))
  (hB : ∀ u ∈ Ioc 0 U, |g u| ≤ B)
include hc₀ hU hg hB

lemma integrable_kx_mul (b c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u => kx c b u * g u) (Ioc 0 U) := by
  refine Integrable.mono' ((integrableOn_kx_Ioc hc b hU.le).const_mul B) ?_ ?_
  · exact ((continuousOn_kx hc b).mono (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self)).mul hg
      |>.aestronglyMeasurable measurableSet_Ioc
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kx_nonneg _ _ _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB u hu) (kx_nonneg _ _ _)

lemma abs_Zr_le (b c : ℝ) (hc : 0 < c) :
    |Zr U c b g| ≤ B * ∫ u in Ioc 0 U, kx c (-b) u := by
  unfold Zr
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_kx_Ioc hc _ hU.le).const_mul B)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kx_nonneg _ _ _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hB u hu) (kx_nonneg _ _ _)

include hδ in
/-- **Taylor expansion of `Z_t[g]`**: `Z_t[g](c₀ + δ) = ∑_l (-δ)^l/l! Z_{t+l}[g](c₀)` for `|δ| < c₀`. -/
theorem hasSum_Zr :
    HasSum (fun l : ℕ => (-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g) (Zr U (c₀ + δ) t g) := by
  have hB0 : 0 ≤ B := by
    have h := hB U ⟨hU, le_rfl⟩; exact (abs_nonneg _).trans h
  have hc' : 0 < c₀ - |δ| := by linarith
  have hint : ∀ l, Integrable (termF c₀ δ t g l) (volume.restrict (Ioc 0 U)) := fun l =>
    (integrable_kx_mul hc₀ hU hg hB _ c₀ hc₀).const_mul _
  have hnorm_le : ∀ l, ∫ u in Ioc 0 U, ‖termF c₀ δ t g l u‖ ≤
      ∫ u in Ioc 0 U, B * (|δ| ^ l / (l ! : ℝ) * kx c₀ (-(t + l)) u) := by
    intro l
    refine setIntegral_mono_on (hint l).norm
      (((integrableOn_kx_Ioc hc₀ _ hU.le).const_mul _).const_mul B) measurableSet_Ioc
      (fun u hu => ?_)
    unfold termF
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (kx_nonneg _ _ _), abs_div, abs_pow,
      abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (l ! : ℝ))]
    have h1 := hB u hu
    have h2 : 0 ≤ |δ| ^ l / (l ! : ℝ) := by positivity
    have h3 := kx_nonneg c₀ (-(t + l)) u
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)]
  have hsum : Summable fun l => ∫ u in Ioc 0 U, ‖termF c₀ δ t g l u‖ := by
    refine summable_of_sum_range_le (c := B * ∫ u in Ioc 0 U, kx (c₀ - |δ|) (-t) u)
      (fun l => integral_nonneg fun u => norm_nonneg _) (fun n => ?_)
    calc ∑ l ∈ Finset.range n, ∫ u in Ioc 0 U, ‖termF c₀ δ t g l u‖
        ≤ ∑ l ∈ Finset.range n, ∫ u in Ioc 0 U, B * (|δ| ^ l / (l ! : ℝ) * kx c₀ (-(t + l)) u) :=
          Finset.sum_le_sum fun l _ => hnorm_le l
      _ = ∫ u in Ioc 0 U, ∑ l ∈ Finset.range n, B * (|δ| ^ l / (l ! : ℝ) * kx c₀ (-(t + l)) u) :=
          (integral_finsetSum _ fun l _ =>
            ((integrableOn_kx_Ioc hc₀ _ hU.le).const_mul _).const_mul B).symm
      _ ≤ ∫ u in Ioc 0 U, B * kx (c₀ - |δ|) (-t) u := by
          refine setIntegral_mono_on (integrable_finsetSum _ fun l _ =>
            ((integrableOn_kx_Ioc hc₀ _ hU.le).const_mul _).const_mul B)
            ((integrableOn_kx_Ioc hc' _ hU.le).const_mul B) measurableSet_Ioc (fun u hu => ?_)
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ hB0
          have hs : ∑ l ∈ Finset.range n, |δ| ^ l / (l ! : ℝ) * kx c₀ (-(t + l)) u =
              kx c₀ (-t) u * ∑ l ∈ Finset.range n, (|δ| / u) ^ l / (l ! : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [kx_add_nat hu.1, div_pow]; simp only [div_eq_mul_inv, inv_pow]; ring
          rw [hs]
          have he := Real.sum_le_exp_of_nonneg (div_nonneg (abs_nonneg δ) hu.1.le) n
          calc kx c₀ (-t) u * ∑ l ∈ Finset.range n, (|δ| / u) ^ l / (l ! : ℝ)
              ≤ kx c₀ (-t) u * rexp (|δ| / u) := mul_le_mul_of_nonneg_left he (kx_nonneg _ _ _)
            _ = _ := by
                rw [kx_of_pos hu.1, kx_of_pos hu.1, mul_assoc, ← exp_add]; congr 2; ring
      _ = _ := integral_const_mul _ _
  have hS := hasSum_integral_of_summable_integral_norm hint hsum
  have hlim : ∫ u in Ioc 0 U, ∑' l, termF c₀ δ t g l u = Zr U (c₀ + δ) t g := by
    unfold Zr
    exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => (hasSum_termF hu.1).tsum_eq)
  rw [hlim] at hS
  convert hS using 1
  ext l
  unfold termF Zr
  rw [integral_const_mul]

/-- The bound `|δ|^l/l! |Z_{t+l}[g](c₀)| ≤ B U^j c₀^{1-t-j} ρ^l` for `l ≥ 2`, `1 ≤ t + j ≤ 2`. -/
lemma abs_taylor_term_le (j : ℕ) (htj1 : 1 ≤ t + j) (htj2 : t + j ≤ 2) {l : ℕ} (hl : 2 ≤ l) :
    |(-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g| ≤
      B * U ^ j * c₀ ^ (1 - t - j) * (|δ| / c₀) ^ l := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB U ⟨hU, le_rfl⟩)
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hint := integral_kx_Ioc_le hc₀ hU j (a := t + l) (by linarith)
  have hG : Real.Gamma (t + l + j - 1) ≤ (l ! : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial, show ((l : ℕ) : ℝ) + 1 = (l : ℝ) + 1 from rfl]
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp only [mem_Ici]; linarith)
      (by simp only [mem_Ici]; linarith) (by linarith)
  have hGpos : 0 < Real.Gamma (t + l + j - 1) := Real.Gamma_pos_of_pos (by linarith)
  have hf : (0 : ℝ) < (l ! : ℝ) := by positivity
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_of_pos hf]
  have hZ := abs_Zr_le hc₀ hU hg hB (t + l) c₀ hc₀
  have hcp : c₀ ^ (t + l + j - 1) = c₀ ^ l * c₀ ^ (t + j - 1) := by
    rw [← rpow_natCast, ← rpow_add hc₀]; congr 1; ring
  have hcm : c₀ ^ (1 - t - j) = (c₀ ^ (t + j - 1))⁻¹ := by
    rw [← rpow_neg hc₀.le]; congr 1; ring
  calc |δ| ^ l / (l ! : ℝ) * |Zr U c₀ (t + l) g|
      ≤ |δ| ^ l / (l ! : ℝ) * (B * (U ^ j * (Real.Gamma (t + l + j - 1) / c₀ ^ (t + l + j - 1)))) := by
        gcongr
        exact hZ.trans (mul_le_mul_of_nonneg_left hint hB0)
    _ ≤ |δ| ^ l / (l ! : ℝ) * (B * (U ^ j * ((l ! : ℝ) / c₀ ^ (t + l + j - 1)))) := by
        gcongr
    _ = _ := by
        rw [hcp, hcm, div_pow]
        field_simp

include hδ in
/-- **Remainder of a Taylor stage**: if `|g| ≤ B` on `(0, U]`, `1 ≤ t + j ≤ 2`, `L ≥ 2` and
`ρ = |δ|/c₀ < 1`, the error after `L` terms of the Taylor series of `Z_t[g]` at `c₀` is at most
`B U^j c₀^{1-t-j} ρ^L/(1-ρ)`. -/
theorem taylor_remainder_le (j : ℕ) (htj1 : 1 ≤ t + j) (htj2 : t + j ≤ 2) {L : ℕ} (hL : 2 ≤ L) :
    |Zr U (c₀ + δ) t g - ∑ l ∈ Finset.range L, (-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g| ≤
      B * U ^ j * c₀ ^ (1 - t - j) * ((|δ| / c₀) ^ L / (1 - |δ| / c₀)) := by
  set ρ := |δ| / c₀
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [div_lt_one hc₀]; exact hδ
  have hS := hasSum_Zr (t := t) hc₀ hδ hU hg hB
  rw [← hS.tsum_eq, ← hS.summable.sum_add_tsum_nat_add L, add_sub_cancel_left]
  have hK : 0 ≤ B * U ^ j * c₀ ^ (1 - t - j) := by
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB U ⟨hU, le_rfl⟩)
    positivity
  have hle : ∀ i, ‖(-δ) ^ (i + L) / ((i + L)! : ℝ) * Zr U c₀ (t + ((i + L : ℕ) : ℝ)) g‖ ≤
      B * U ^ j * c₀ ^ (1 - t - j) * ρ ^ L * ρ ^ i := by
    intro i
    rw [Real.norm_eq_abs, mul_assoc, ← pow_add, add_comm L i]
    exact abs_taylor_term_le hc₀ hU hg hB j htj1 htj2 (by omega)
  have hg' : Summable fun i : ℕ => B * U ^ j * c₀ ^ (1 - t - j) * ρ ^ L * ρ ^ i :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  rw [← Real.norm_eq_abs]
  calc ‖∑' i, (-δ) ^ (i + L) / ((i + L)! : ℝ) * Zr U c₀ (t + ((i + L : ℕ) : ℝ)) g‖
      ≤ ∑' i : ℕ, B * U ^ j * c₀ ^ (1 - t - j) * ρ ^ L * ρ ^ i := tsum_of_norm_bounded hg'.hasSum hle
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]; ring

end Taylor

/-- **The paper's form** (Section 6.4.2, "Taylor stages"): for the state components
(`t = 3/2`, or `t = 1/2`), `|g| ≤ e^{4U}`, `U ≤ 2`, `L ≥ 2`, the error after `L` terms is at most
`2 e^{4U} ρ^L/(c₀^{1/2}(1-ρ))`. -/
theorem taylor_remainder_paper {U c₀ δ t : ℝ} {g : ℝ → ℝ} (hc₀ : 0 < c₀) (hδ : |δ| < c₀)
    (hU : 0 < U) (hU2 : U ≤ 2) (hg : ContinuousOn g (Ioc 0 U))
    (hB : ∀ u ∈ Ioc 0 U, |g u| ≤ rexp (4 * U)) (ht : t = 3 / 2 ∨ t = 1 / 2) {L : ℕ} (hL : 2 ≤ L) :
    |Zr U (c₀ + δ) t g - ∑ l ∈ Finset.range L, (-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g| ≤
      2 * rexp (4 * U) * ((|δ| / c₀) ^ L / (c₀ ^ (1 / 2 : ℝ) * (1 - |δ| / c₀))) := by
  have hρ1 : |δ| / c₀ < 1 := by rw [div_lt_one hc₀]; exact hδ
  have hq : 0 ≤ (|δ| / c₀) ^ L / (1 - |δ| / c₀) := div_nonneg (by positivity) (by linarith)
  have hcm : c₀ ^ (-(1 / 2 : ℝ)) = (c₀ ^ (1 / 2 : ℝ))⁻¹ := rpow_neg hc₀.le _
  have hc12 : 0 < c₀ ^ (1 / 2 : ℝ) := rpow_pos_of_pos hc₀ _
  have hE := exp_pos (4 * U)
  have hrhs : 2 * rexp (4 * U) * ((|δ| / c₀) ^ L / (c₀ ^ (1 / 2 : ℝ) * (1 - |δ| / c₀))) =
      2 * rexp (4 * U) * c₀ ^ (-(1 / 2 : ℝ)) * ((|δ| / c₀) ^ L / (1 - |δ| / c₀)) := by
    rw [hcm]; field_simp
  rw [hrhs]
  rcases ht with rfl | rfl
  · refine (taylor_remainder_le hc₀ hδ hU hg hB 0 (by norm_num) (by norm_num) hL).trans ?_
    rw [pow_zero, mul_one, show (1 : ℝ) - 3 / 2 - ((0 : ℕ) : ℝ) = -(1 / 2) by norm_num]
    gcongr
    linarith
  · refine (taylor_remainder_le hc₀ hδ hU hg hB 1 (by norm_num) (by norm_num) hL).trans ?_
    rw [pow_one, show (1 : ℝ) - 1 / 2 - ((1 : ℕ) : ℝ) = -(1 / 2) by norm_num]
    have h0 : 0 ≤ c₀ ^ (-(1 / 2 : ℝ)) := by positivity
    have : rexp (4 * U) * U * c₀ ^ (-(1 / 2 : ℝ)) ≤ 2 * rexp (4 * U) * c₀ ^ (-(1 / 2 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hU2 (mul_nonneg hE.le h0)
      nlinarith
    exact mul_le_mul_of_nonneg_right this hq

/-! ### The refined bound with the factor `E = e^{-c₀/U}` -/

/-- `∫_0^U u^{-b} e^{-c/u} du ≤ 2 e^{-c/U} U^{2-b}/c` when `b ≥ 2` and `(b-2)U ≤ c/2`
(from `(Drec)`; the incomplete-gamma bound `Γ(a,y) ≤ y^{a-1}e^{-y}/(1-(a-1)/y)` in the paper). -/
theorem Dint_le_E {c U b : ℝ} (hc : 0 < c) (hU : 0 < U) (hb : 2 ≤ b) (hbU : (b - 2) * U ≤ c / 2) :
    Dint c U (1 - b) ≤ 2 * rexp (-(c / U)) * U ^ (2 - b) / c := by
  have hrec := Drec hc hU (2 - b)
  rw [show 2 - b - 1 = 1 - b by ring] at hrec
  have hmono : Dint c U (2 - b) ≤ U * Dint c U (1 - b) := by
    unfold Dint
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hU.le (intervalIntegrable_kx hc _ hU.le)
      ((intervalIntegrable_kx hc _ hU.le).const_mul U) (fun u hu => ?_)
    rcases hu.1.eq_or_lt with h | h
    · subst h; simp [kx]
    · rw [kx_of_pos h, kx_of_pos h, show 2 - b - 1 = 1 + (1 - b - 1) by ring, rpow_add h, rpow_one]
      have h0 : 0 ≤ u ^ (1 - b - 1) * rexp (-(c / u)) :=
        mul_nonneg (rpow_nonneg h.le _) (exp_pos _).le
      calc u * u ^ (1 - b - 1) * rexp (-(c / u)) = u * (u ^ (1 - b - 1) * rexp (-(c / u))) := by ring
        _ ≤ U * (u ^ (1 - b - 1) * rexp (-(c / u))) := mul_le_mul_of_nonneg_right hu.2 h0
  have hD := (Dint_pos hc hU (1 - b)).le
  have hD2 := (Dint_pos hc hU (2 - b)).le
  have key : c * Dint c U (1 - b) ≤ rexp (-(c / U)) * U ^ (2 - b) + c / 2 * Dint c U (1 - b) := by
    have h1 : (b - 2) * Dint c U (2 - b) ≤ (b - 2) * (U * Dint c U (1 - b)) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    have h2 : (b - 2) * (U * Dint c U (1 - b)) ≤ c / 2 * Dint c U (1 - b) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbU hD
    linarith
  rw [le_div_iff₀ hc]
  linarith

section Refined

variable {U c₀ δ t B : ℝ} {g : ℝ → ℝ}
variable (hc₀ : 0 < c₀) (hδ : |δ| < c₀) (hU : 0 < U) (hg : ContinuousOn g (Ioc 0 U))
  (hB : ∀ u ∈ Ioc 0 U, |g u| ≤ B)
include hc₀ hU hg hB

lemma integral_kx_Ioc_eq_Dint (c b : ℝ) : ∫ u in Ioc 0 U, kx c (-b) u = Dint c U (1 - b) := by
  unfold Dint; rw [intervalIntegral.integral_of_le hU.le]; congr 1; ext u; congr 1; ring

/-- The term bound `|δ|^l/l! |Z_{t+l}[g](c₀)| ≤ 2 B E U^{2-t} (|δ|/U)^l/(l! c₀)`, for
`t + l ≥ 2` and `(t + l - 2) U ≤ c₀/2`. -/
lemma abs_taylor_term_le_E {l : ℕ} (htl : 2 ≤ t + l) (htlU : (t + l - 2) * U ≤ c₀ / 2) :
    |(-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g| ≤
      2 * B * rexp (-(c₀ / U)) * U ^ (2 - t) / c₀ * ((|δ| / U) ^ l / (l ! : ℝ)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB U ⟨hU, le_rfl⟩)
  have hZ := abs_Zr_le hc₀ hU hg hB (t + l) c₀ hc₀
  rw [integral_kx_Ioc_eq_Dint hc₀ hU hg hB] at hZ
  have hD := Dint_le_E hc₀ hU htl htlU
  have hf : (0 : ℝ) < (l ! : ℝ) := by positivity
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_of_pos hf]
  have hUp : U ^ (2 - (t + l)) = U ^ (2 - t) / U ^ l := by
    rw [show 2 - (t + l) = (2 - t) - (l : ℝ) by ring, rpow_sub hU, rpow_natCast]
  calc |δ| ^ l / (l ! : ℝ) * |Zr U c₀ (t + l) g|
      ≤ |δ| ^ l / (l ! : ℝ) * (B * (2 * rexp (-(c₀ / U)) * U ^ (2 - (t + l)) / c₀)) := by
        gcongr
        exact hZ.trans (mul_le_mul_of_nonneg_left hD hB0)
    _ = _ := by rw [hUp, div_pow]; field_simp

include hδ in
/-- **Refined remainder of a Taylor stage** (Section 6.4.2, second bound). Let `1/2 ≤ t ≤ 3/2`,
`1 ≤ t + j ≤ 2`, `L ≥ 2`, `|δ| ≤ (L+1)U/2` and `l₁ = ⌊c₀/(2U)⌋ + 1`. Then the error after `L` terms
is at most `4 B E U^{2-t} (|δ|/U)^L/(L! c₀) + B U^j c₀^{1-t-j} ρ^{l₁}/(1-ρ)`. -/
theorem taylor_remainder_le_E (j : ℕ) (ht1 : 1 / 2 ≤ t) (ht2 : t ≤ 3 / 2) (htj1 : 1 ≤ t + j)
    (htj2 : t + j ≤ 2) {L : ℕ} (hL : 2 ≤ L) (hδU : |δ| ≤ ((L : ℝ) + 1) * U / 2) :
    |Zr U (c₀ + δ) t g - ∑ l ∈ Finset.range L, (-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g| ≤
      4 * B * rexp (-(c₀ / U)) * U ^ (2 - t) / c₀ * ((|δ| / U) ^ L / (L ! : ℝ)) +
      B * U ^ j * c₀ ^ (1 - t - j) * ((|δ| / c₀) ^ (⌊c₀ / (2 * U)⌋₊ + 1) / (1 - |δ| / c₀)) := by
  set ρ := |δ| / c₀
  set l₁ := ⌊c₀ / (2 * U)⌋₊ + 1
  set A := 2 * B * rexp (-(c₀ / U)) * U ^ (2 - t) / c₀
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB U ⟨hU, le_rfl⟩)
  have hA0 : 0 ≤ A := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [div_lt_one hc₀]; exact hδ
  set T : ℕ → ℝ := fun l => (-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g
  have hS : HasSum T (Zr U (c₀ + δ) t g) := hasSum_Zr (t := t) hc₀ hδ hU hg hB
  set M := max L l₁
  obtain ⟨d, hd⟩ : ∃ d, M = L + d := ⟨M - L, by omega⟩
  rw [← hS.tsum_eq, ← hS.summable.sum_add_tsum_nat_add L, add_sub_cancel_left]
  have hsL : Summable fun i => T (i + L) := (summable_nat_add_iff L).2 hS.summable
  rw [← hsL.sum_add_tsum_nat_add d]
  -- the first block: `L ≤ l < M`, with the factor `E`
  have hq : ∀ i, (|δ| / U) ^ (L + i) / ((L + i)! : ℝ) ≤ (|δ| / U) ^ L / (L ! : ℝ) * (1 / 2) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [← add_assoc, pow_succ, Nat.factorial_succ, pow_succ]; push_cast
      have hr : |δ| / U / ((L : ℝ) + i + 1) ≤ 1 / 2 := by
        rw [div_div, div_le_iff₀ (by positivity)]
        have : ((L : ℝ) + 1) ≤ (L : ℝ) + i + 1 := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
        nlinarith
      have hf : (0 : ℝ) < ((L + i)! : ℝ) := by positivity
      calc (|δ| / U) ^ (L + i) * (|δ| / U) / (((L : ℝ) + i + 1) * ((L + i)! : ℝ))
          = (|δ| / U) ^ (L + i) / ((L + i)! : ℝ) * (|δ| / U / ((L : ℝ) + i + 1)) := by
            field_simp
        _ ≤ (|δ| / U) ^ L / (L ! : ℝ) * (1 / 2) ^ i * (1 / 2) := by
            gcongr
        _ = _ := by ring
  have hblock1 : |∑ i ∈ Finset.range d, T (i + L)| ≤ A * (2 * ((|δ| / U) ^ L / (L ! : ℝ))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range d, |T (i + L)|
        ≤ ∑ i ∈ Finset.range d, A * ((|δ| / U) ^ L / (L ! : ℝ) * (1 / 2) ^ i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have hlt : i + L < l₁ := by
            have h2 : i + L < max L l₁ := by have : i + L < M := by omega
                                             exact this
            rcases lt_max_iff.1 h2 with h | h
            · omega
            · exact h
          have hl1 : ((i + L : ℕ) : ℝ) ≤ c₀ / (2 * U) := by
            have h1 : i + L ≤ ⌊c₀ / (2 * U)⌋₊ := by omega
            exact (Nat.cast_le.2 h1).trans (Nat.floor_le (by positivity))
          have hL2 : (2 : ℝ) ≤ ((i + L : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ i + L)
          have htl : 2 ≤ t + ((i + L : ℕ) : ℝ) := by linarith
          have htlU : (t + ((i + L : ℕ) : ℝ) - 2) * U ≤ c₀ / 2 := by
            have h1 : ((i + L : ℕ) : ℝ) * (2 * U) ≤ c₀ := by
              rwa [le_div_iff₀ (by positivity)] at hl1
            nlinarith
          refine (abs_taylor_term_le_E hc₀ hU hg hB htl htlU).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ hA0
          have := hq i
          rwa [add_comm L i] at this
      _ = A * ((|δ| / U) ^ L / (L ! : ℝ)) * ∑ i ∈ Finset.range d, (1 / 2 : ℝ) ^ i := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ A * ((|δ| / U) ^ L / (L ! : ℝ)) * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := sum_geometric_two_le d
          simpa using this
      _ = _ := by ring
  -- the second block: `l ≥ M ≥ l₁`, geometric in `ρ`
  have hblock2 : |∑' i, T (i + d + L)| ≤ B * U ^ j * c₀ ^ (1 - t - j) * (ρ ^ l₁ / (1 - ρ)) := by
    have hK : 0 ≤ B * U ^ j * c₀ ^ (1 - t - j) := by positivity
    have hle : ∀ i, ‖T (i + d + L)‖ ≤ B * U ^ j * c₀ ^ (1 - t - j) * ρ ^ l₁ * ρ ^ i := by
      intro i
      rw [Real.norm_eq_abs]
      refine (abs_taylor_term_le hc₀ hU hg hB j htj1 htj2 (by omega)).trans ?_
      rw [mul_assoc (B * U ^ j * c₀ ^ (1 - t - j)), ← pow_add]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1.le ?_) hK
      have : l₁ ≤ M := le_max_right _ _
      omega
    have hg' : Summable fun i : ℕ => B * U ^ j * c₀ ^ (1 - t - j) * ρ ^ l₁ * ρ ^ i :=
      (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
    rw [← Real.norm_eq_abs]
    calc ‖∑' i, T (i + d + L)‖ ≤ ∑' i : ℕ, B * U ^ j * c₀ ^ (1 - t - j) * ρ ^ l₁ * ρ ^ i :=
          tsum_of_norm_bounded hg'.hasSum hle
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]; ring
  calc |∑ i ∈ Finset.range d, T (i + L) + ∑' i, T (i + d + L)|
      ≤ |∑ i ∈ Finset.range d, T (i + L)| + |∑' i, T (i + d + L)| := abs_add_le _ _
    _ ≤ A * (2 * ((|δ| / U) ^ L / (L ! : ℝ))) + B * U ^ j * c₀ ^ (1 - t - j) * (ρ ^ l₁ / (1 - ρ)) :=
        add_le_add hblock1 hblock2
    _ = _ := by simp only [A]; ring

end Refined

/-- **The paper's second form** (Section 6.4.2, "Taylor stages"): for `t ∈ {3/2, 1/2}`,
`|g| ≤ e^{4U}`, `U ≤ 2`, `L ≥ 2` and `|δ| ≤ (L+1)U/2` (e.g. `|δ| ≤ U`), the error after `L` terms is
at most `8e^{4U}E (|δ|/U)^L/L! (U^{1/2}/c₀ + U^{3/2}/c₀²) + 2e^{4U}ρ^{⌊c₀/(2U)⌋+1}/(c₀^{1/2}(1-ρ))`.
Without a bound on `|δ|/U` this fails for `δ < 0` (e.g. `t = 3/2`, `c₀ = 22.2`, `U = 1/16`,
`δ = -2`, `L = 2`: error `6.8·10^{-143}`, bound `3.3·10^{-153}`). -/
theorem taylor_remainder_paper_E {U c₀ δ t : ℝ} {g : ℝ → ℝ} (hc₀ : 0 < c₀) (hδ : |δ| < c₀)
    (hU : 0 < U) (hU2 : U ≤ 2) (hg : ContinuousOn g (Ioc 0 U))
    (hB : ∀ u ∈ Ioc 0 U, |g u| ≤ rexp (4 * U)) (ht : t = 3 / 2 ∨ t = 1 / 2) {L : ℕ} (hL : 2 ≤ L)
    (hδU : |δ| ≤ ((L : ℝ) + 1) * U / 2) :
    |Zr U (c₀ + δ) t g - ∑ l ∈ Finset.range L, (-δ) ^ l / (l ! : ℝ) * Zr U c₀ (t + l) g| ≤
      8 * rexp (4 * U) * rexp (-(c₀ / U)) * ((|δ| / U) ^ L / (L ! : ℝ)) *
          (U ^ (1 / 2 : ℝ) / c₀ + U ^ (3 / 2 : ℝ) / c₀ ^ 2) +
        2 * rexp (4 * U) * ((|δ| / c₀) ^ (⌊c₀ / (2 * U)⌋₊ + 1) /
          (c₀ ^ (1 / 2 : ℝ) * (1 - |δ| / c₀))) := by
  have hρ1 : |δ| / c₀ < 1 := by rw [div_lt_one hc₀]; exact hδ
  set q := (|δ| / c₀) ^ (⌊c₀ / (2 * U)⌋₊ + 1) / (1 - |δ| / c₀)
  have hq : 0 ≤ q := div_nonneg (by positivity) (by linarith)
  set P := (|δ| / U) ^ L / (L ! : ℝ)
  have hP : 0 ≤ P := by positivity
  have hcm : c₀ ^ (-(1 / 2 : ℝ)) = (c₀ ^ (1 / 2 : ℝ))⁻¹ := rpow_neg hc₀.le _
  have hc12 : 0 < c₀ ^ (1 / 2 : ℝ) := rpow_pos_of_pos hc₀ _
  have hE := exp_pos (4 * U)
  have hEc := exp_pos (-(c₀ / U))
  have hrhs : 2 * rexp (4 * U) * ((|δ| / c₀) ^ (⌊c₀ / (2 * U)⌋₊ + 1) /
      (c₀ ^ (1 / 2 : ℝ) * (1 - |δ| / c₀))) = 2 * rexp (4 * U) * c₀ ^ (-(1 / 2 : ℝ)) * q := by
    rw [hcm]; simp only [q]; field_simp
  rw [hrhs]
  have hU12 : 0 ≤ U ^ (3 / 2 : ℝ) / c₀ ^ 2 := by positivity
  have hX : 0 ≤ rexp (4 * U) * rexp (-(c₀ / U)) * P := by positivity
  have h0 : 0 ≤ c₀ ^ (-(1 / 2 : ℝ)) := by positivity
  rcases ht with rfl | rfl
  · refine (taylor_remainder_le_E hc₀ hδ hU hg hB 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hL hδU).trans ?_
    rw [pow_zero, mul_one, show (1 : ℝ) - 3 / 2 - ((0 : ℕ) : ℝ) = -(1 / 2) by norm_num,
      show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num]
    have e1 : 4 * rexp (4 * U) * rexp (-(c₀ / U)) * U ^ (1 / 2 : ℝ) / c₀ * P ≤
        8 * rexp (4 * U) * rexp (-(c₀ / U)) * P * (U ^ (1 / 2 : ℝ) / c₀ + U ^ (3 / 2 : ℝ) / c₀ ^ 2) := by
      have ha : 0 ≤ U ^ (1 / 2 : ℝ) / c₀ := by positivity
      have l1 : 4 * rexp (4 * U) * rexp (-(c₀ / U)) * U ^ (1 / 2 : ℝ) / c₀ * P =
          4 * ((rexp (4 * U) * rexp (-(c₀ / U)) * P) * (U ^ (1 / 2 : ℝ) / c₀)) := by ring
      have l2 : 8 * rexp (4 * U) * rexp (-(c₀ / U)) * P * (U ^ (1 / 2 : ℝ) / c₀ + U ^ (3 / 2 : ℝ) / c₀ ^ 2) =
          8 * ((rexp (4 * U) * rexp (-(c₀ / U)) * P) * (U ^ (1 / 2 : ℝ) / c₀)) +
            8 * ((rexp (4 * U) * rexp (-(c₀ / U)) * P) * (U ^ (3 / 2 : ℝ) / c₀ ^ 2)) := by ring
      rw [l1, l2]
      nlinarith [mul_nonneg hX ha, mul_nonneg hX hU12]
    have e2 : rexp (4 * U) * c₀ ^ (-(1 / 2 : ℝ)) * q ≤ 2 * rexp (4 * U) * c₀ ^ (-(1 / 2 : ℝ)) * q := by
      nlinarith [mul_nonneg (mul_nonneg hE.le h0) hq]
    linarith
  · refine (taylor_remainder_le_E hc₀ hδ hU hg hB 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hL hδU).trans ?_
    rw [pow_one, show (1 : ℝ) - 1 / 2 - ((1 : ℕ) : ℝ) = -(1 / 2) by norm_num,
      show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num]
    have hU32 : U ^ (3 / 2 : ℝ) ≤ 2 * U ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hU, rpow_one]
      exact mul_le_mul_of_nonneg_right hU2 (by positivity)
    have e1 : 4 * rexp (4 * U) * rexp (-(c₀ / U)) * U ^ (3 / 2 : ℝ) / c₀ * P ≤
        8 * rexp (4 * U) * rexp (-(c₀ / U)) * P * (U ^ (1 / 2 : ℝ) / c₀ + U ^ (3 / 2 : ℝ) / c₀ ^ 2) := by
      have h1 : U ^ (3 / 2 : ℝ) / c₀ ≤ 2 * (U ^ (1 / 2 : ℝ) / c₀) := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hU32 hc₀.le
      have : 4 * rexp (4 * U) * rexp (-(c₀ / U)) * U ^ (3 / 2 : ℝ) / c₀ * P =
          4 * (rexp (4 * U) * rexp (-(c₀ / U)) * P) * (U ^ (3 / 2 : ℝ) / c₀) := by ring
      have l2 : 8 * rexp (4 * U) * rexp (-(c₀ / U)) * P * (U ^ (1 / 2 : ℝ) / c₀ + U ^ (3 / 2 : ℝ) / c₀ ^ 2) =
          8 * ((rexp (4 * U) * rexp (-(c₀ / U)) * P) * (U ^ (1 / 2 : ℝ) / c₀)) +
            8 * ((rexp (4 * U) * rexp (-(c₀ / U)) * P) * (U ^ (3 / 2 : ℝ) / c₀ ^ 2)) := by ring
      rw [this, l2]
      nlinarith [mul_le_mul_of_nonneg_left h1 hX, mul_nonneg hX hU12]
    have e2 : rexp (4 * U) * U * c₀ ^ (-(1 / 2 : ℝ)) * q ≤ 2 * rexp (4 * U) * c₀ ^ (-(1 / 2 : ℝ)) * q := by
      have := mul_le_mul_of_nonneg_left hU2 (mul_nonneg (mul_nonneg hE.le h0) hq)
      nlinarith
    linarith

end ZetaF.TaylorStage
