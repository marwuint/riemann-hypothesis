import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.PerfectoidField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a b u : ℤ → K} {ρ : ℝ}

theorem gaussNorm_cmul_le (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    gaussNorm (cmul a b) ρ ≤ gaussNorm a ρ * gaussNorm b ρ :=
  gaussNorm_le fun n => norm_cmul_mul_zpow_le hρ
    (mul_nonneg (gaussNorm_nonneg hρ) (gaussNorm_nonneg hρ)) fun i =>
      mul_le_mul (ha.le_gaussNorm i) (hb.le_gaussNorm _) (by positivity) (gaussNorm_nonneg hρ)

def cpow (u : ℤ → K) : ℕ → ℤ → K
  | 0 => Pi.single 0 1
  | k + 1 => cmul u (cpow u k)

theorem ConvergesAt.cpow (hρ : 0 < ρ) (hu : ConvergesAt u ρ) : ∀ k, ConvergesAt (cpow u k) ρ
  | 0 => convergesAt_single 0 1 ρ
  | k + 1 => hu.cmul hρ (hu.cpow hρ k)

theorem gaussNorm_cpow_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) :
    ∀ k, gaussNorm (cpow u k) ρ ≤ gaussNorm u ρ ^ k
  | 0 => by simp [cpow, gaussNorm_single_zero_one hρ]
  | k + 1 => by
    rw [pow_succ']
    exact (gaussNorm_cmul_le hρ hu (hu.cpow hρ k)).trans
      (mul_le_mul_of_nonneg_left (gaussNorm_cpow_le hρ hu k) (gaussNorm_nonneg hρ))

theorem weight_cpow_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (k : ℕ) (n : ℤ) :
    ‖cpow u k n‖ * ρ ^ n ≤ gaussNorm u ρ ^ k :=
  ((hu.cpow hρ k).le_gaussNorm n).trans (gaussNorm_cpow_le hρ hu k)

def geomInv (u : ℤ → K) : ℤ → K := fun n => ∑' k : ℕ, (-1) ^ k * cpow u k n

theorem norm_geom_term_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (k : ℕ) (n : ℤ) :
    ‖(-1) ^ k * cpow u k n‖ ≤ gaussNorm u ρ ^ k / ρ ^ n := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_div_iff₀ (zpow_pos hρ n)]
  exact weight_cpow_le hρ hu k n

theorem tendsto_geom_term (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) (n : ℤ) :
    Tendsto (fun k : ℕ => (-1) ^ k * cpow u k n) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Nat.cofinite_eq_atTop]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (gaussNorm_nonneg hρ) hq).div_const (ρ ^ n)
  rw [zero_div] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_geom_term_le hρ hu k n) h

theorem ConvergesAt.geomInv (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) :
    ConvergesAt (geomInv u) ρ := by
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun n =>
    lt_of_lt_of_le hx (by positivity), fun ε hε => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (half_pos hε) hq
  have hS : (⋃ k ∈ Finset.range k₀, {n : ℤ | ε / 2 ≤ ‖Laurent.cpow u k n‖ * ρ ^ n}).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun k _ => (hu.cpow hρ k).finite_le (half_pos hε)
  refine Filter.eventually_cofinite.2 (hS.subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hn
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, not_exists, not_and, not_le]
    at hcon
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  have : ‖Laurent.geomInv u n‖ * ρ ^ n ≤ ε / 2 := by
    rw [← le_div_iff₀ hρn]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_div_iff₀ hρn]
    rcases lt_or_ge k k₀ with hk | hk
    · exact (hcon k hk).le
    · exact (weight_cpow_le hρ hu k n).trans ((pow_le_pow_of_le_one (gaussNorm_nonneg hρ)
        hq.le hk).trans hk₀.le)
  linarith

theorem cmul_one_add_geomInv (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) :
    cmul (Pi.single 0 1 + u) (geomInv u) = Pi.single 0 1 := by
  have hw := hu.geomInv hρ hq
  rw [add_cmul hρ (convergesAt_single 0 1 ρ) hu hw, single_zero_one_cmul]
  funext n
  have hsum : Summable (Function.uncurry fun i (k : ℕ) => u i * ((-1) ^ k * cpow u k (n - i))) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hq' : Tendsto (fun k : ℕ => gaussNorm u ρ ^ k) cofinite (𝓝 0) := by
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (gaussNorm_nonneg hρ) hq
    have h := (tendsto_mul_cofinite_nhds_zero hu hq').div_const (ρ ^ n)
    rw [zero_div] at h
    refine squeeze_zero (fun _ => norm_nonneg _) (fun ⟨i, k⟩ => ?_) h
    simp only [Function.uncurry_apply_pair, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    have hρn : 0 < ρ ^ n := zpow_pos hρ n
    rw [le_div_iff₀ hρn]
    have e : ρ ^ n = ρ ^ i * ρ ^ (n - i) := by rw [← zpow_add₀ hρ.ne']; congr 1; ring
    rw [e]
    have h1 := weight_cpow_le hρ hu k (n - i)
    calc ‖u i‖ * ‖cpow u k (n - i)‖ * (ρ ^ i * ρ ^ (n - i))
        = (‖u i‖ * ρ ^ i) * (‖cpow u k (n - i)‖ * ρ ^ (n - i)) := by ring
      _ ≤ (‖u i‖ * ρ ^ i) * gaussNorm u ρ ^ k :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
  have e1 : cmul u (geomInv u) n = ∑' k : ℕ, (-1) ^ k * cpow u (k + 1) n := by
    simp only [cmul, geomInv, cpow]
    simp_rw [← tsum_mul_left]
    rw [← hsum.tsum_comm]
    congr 1; funext k
    congr 1; funext i; ring
  have e2 : geomInv u n = (Pi.single 0 (1 : K) : ℤ → K) n - ∑' k : ℕ, (-1) ^ k * cpow u (k + 1) n := by
    unfold geomInv
    rw [NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_geom_term hρ hu hq n) |>.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, cpow, pow_succ, mul_neg, mul_one, neg_mul, tsum_neg]
    ring
  rw [Pi.add_apply, e1, e2, Pi.single_apply]
  ring

end Laurent

namespace Robba

instance : Nontrivial (Robba K) :=
  ⟨⟨0, 1, fun h => by simpa using congrFun (congrArg Robba.coeff h) 0⟩⟩

theorem isUnit_one_add {U : Robba K} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hU : ∀ ρ, s ≤ ρ → ρ < 1 → ConvergesAt U.coeff ρ ∧ gaussNorm U.coeff ρ < 1) :
    IsUnit (1 + U) := by
  let W : Robba K := ⟨geomInv U.coeff, ⟨s, hs1, fun ρ h1 h2 h3 =>
    (hU ρ h1 h2).1.geomInv h3 (hU ρ h1 h2).2⟩⟩
  have h : (1 + U) * W = 1 :=
    Robba.ext (cmul_one_add_geomInv hs0 (hU s le_rfl hs1).1 (hU s le_rfl hs1).2)
  exact ⟨⟨_, W, h, by rw [mul_comm]; exact h⟩, rfl⟩

end Robba

theorem exists_norm_le_mul_of_lt [IsDiscreteValuationRing (normInteger K)] :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x y : K, ‖y‖ < ‖x‖ → ‖y‖ ≤ q * ‖x‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hunit : ∀ z : normInteger K, IsUnit z ↔ ‖(z : K)‖ = 1 := by
    intro z
    rw [normInteger_integers.isUnit_iff_valuation_eq_one, NormedField.valuation_apply,
      ← NNReal.coe_eq_one]
    rfl
  have hϖ1 : ‖(ϖ : K)‖ < 1 :=
    lt_of_le_of_ne (mem_normInteger.1 ϖ.2) fun h => hϖ.not_isUnit ((hunit ϖ).2 h)
  refine ⟨‖(ϖ : K)‖, norm_nonneg _, hϖ1, fun x y hxy => ?_⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hxy
    exact absurd hxy (not_lt.2 (norm_nonneg _))
  have hz : ‖y / x‖ < 1 := by rw [norm_div, div_lt_one (norm_pos_iff.2 hx)]; exact hxy
  let z : normInteger K := ⟨y / x, mem_normInteger.2 hz.le⟩
  have hzmem : z ∈ IsLocalRing.maximalIdeal (normInteger K) :=
    (IsLocalRing.mem_maximalIdeal z).2 (mem_nonunits_iff.2 fun hu => hz.ne ((hunit z).1 hu))
  rw [hmax, Ideal.mem_span_singleton'] at hzmem
  obtain ⟨t, ht⟩ := hzmem
  have e : y / x = (t : K) * (ϖ : K) := (congrArg Subtype.val ht).symm
  have ht1 : ‖(t : K)‖ ≤ 1 := mem_normInteger.1 t.2
  have : ‖y‖ = ‖y / x‖ * ‖x‖ := by rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]
  rw [this, e, norm_mul]
  calc ‖(t : K)‖ * ‖(ϖ : K)‖ * ‖x‖ = ‖(t : K)‖ * (‖(ϖ : K)‖ * ‖x‖) := by ring
    _ ≤ 1 * (‖(ϖ : K)‖ * ‖x‖) := mul_le_mul_of_nonneg_right ht1 (by positivity)
    _ = ‖(ϖ : K)‖ * ‖x‖ := one_mul _

namespace Robba

end Robba

end GroundTheory.PAdicHodge
