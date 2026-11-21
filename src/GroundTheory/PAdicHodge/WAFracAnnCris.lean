import Mathlib
import GroundTheory.PAdicHodge.WAFracAnn
import GroundTheory.PAdicHodge.WAPeriodT
import GroundTheory.PAdicHodge.BCrisNewtonApprox
import GroundTheory.PAdicHodge.ACrisGalois
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

end TeichLift

namespace WAFrac

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0)

def awayToAnn : 𝔸 →+* (𝓣).Ann ρ0 σ0 := (𝓣).coeAnn.comp (awayToEcon p ρ0)

variable {ρ0 σ0}

theorem annNorm_awayToAnn (r : AnnRad ρ0 σ0) (z : 𝔸) :
    (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 z) = gn ℂ_[p] p r z :=
  (𝓣).annNorm_coeAnn r _

theorem rad_pos' (r : AnnRad ρ0 σ0) : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1

theorem rad_lt_one' (r : AnnRad ρ0 σ0) : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2

variable (hσ : (p : ℝ)⁻¹ ≤ σ0)
include hσ

theorem norm_p_le_rad (r : AnnRad ρ0 σ0) : ‖(p : ℂ_[p])‖ ≤ r := by
  rw [norm_natCast_p]; exact hσ.trans r.2.1

theorem annNorm_awayToAnn_le_one (r : AnnRad ρ0 σ0) {z : 𝔸} (hz : z ∈ ACrisZero ℂ_[p] p) :
    (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 z) ≤ 1 := by
  rw [annNorm_awayToAnn]
  exact gn_acrisZero_le_one (norm_p_le_rad hσ r) (rad_pos' r) (rad_lt_one' r) hz

theorem annNorm_awayToAnn_sub_le (r : AnnRad ρ0 σ0) {c₁ c₂ : ACrisZero ℂ_[p] p} {N : ℕ}
    (h : algebraMap _ (ACris ℂ_[p] p) c₁ - algebraMap _ (ACris ℂ_[p] p) c₂ ∈
      Ideal.span {(p : ACris ℂ_[p] p) ^ N}) :
    (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (c₁ : 𝔸) - awayToAnn ρ0 σ0 (c₂ : 𝔸)) ≤ (r : ℝ) ^ N := by
  rw [← map_sub, annNorm_awayToAnn]
  exact gn_sub_le_of_mem (norm_p_le_rad hσ r) (rad_lt_one' r) h

omit hσ in

def acrisApprox (a : ACris ℂ_[p] p) (N : ℕ) : ACrisZero ℂ_[p] p := (exists_approx a N).choose

omit hσ in
theorem acrisApprox_spec (a : ACris ℂ_[p] p) (N : ℕ) :
    a - algebraMap _ (ACris ℂ_[p] p) (acrisApprox a N) ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} :=
  (exists_approx a N).choose_spec

omit hσ in
theorem sub_mem_span_of_le {a : ACris ℂ_[p] p} {c₁ c₂ : ACrisZero ℂ_[p] p} {M N : ℕ} (hMN : M ≤ N)
    (h₁ : a - algebraMap _ (ACris ℂ_[p] p) c₁ ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ M})
    (h₂ : a - algebraMap _ (ACris ℂ_[p] p) c₂ ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N}) :
    algebraMap _ (ACris ℂ_[p] p) c₂ - algebraMap _ (ACris ℂ_[p] p) c₁ ∈
      Ideal.span {(p : ACris ℂ_[p] p) ^ M} := by
  have h₂' : a - algebraMap _ (ACris ℂ_[p] p) c₂ ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ M} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hMN) h₂
  have := sub_mem h₁ h₂'
  rwa [sub_sub_sub_cancel_left] at this

theorem rad_pow_le (r : AnnRad ρ0 σ0) (N : ℕ) : (r : ℝ) ^ N ≤ (ρ0 : ℝ) ^ N :=
  pow_le_pow_left₀ (rad_pos' r).le r.2.2 N

theorem exists_acrisLimit (a : ACris ℂ_[p] p) :
    ∃ x : (𝓣).Ann ρ0 σ0, ∀ r : AnnRad ρ0 σ0,
      Tendsto (fun N => (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸) - x)) atTop (𝓝 0) := by
  refine (𝓣).exists_limit_ann fun ε hε => ?_
  obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one hε ρ0.2.2
  have key : ∀ r : AnnRad ρ0 σ0, ∀ J ≥ J₀, ∀ K ≥ J₀, (𝓣).annNorm ρ0 σ0 r
      (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - awayToAnn ρ0 σ0 (acrisApprox a K : 𝔸)) ≤ ε := by
    intro r J hJ K hK
    have hle : ∀ M N, M ≤ N → (𝓣).annNorm ρ0 σ0 r
        (awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸) - awayToAnn ρ0 σ0 (acrisApprox a M : 𝔸)) ≤
          (r : ℝ) ^ M := fun M N hMN =>
      annNorm_awayToAnn_sub_le hσ r (sub_mem_span_of_le hMN (acrisApprox_spec a M) (acrisApprox_spec a N))
    have hJ' : (r : ℝ) ^ J₀ ≤ ε := ((rad_pow_le hσ r J₀).trans hJ₀.le)
    rcases le_total J K with h | h
    · rw [(𝓣).annNorm_sub_comm]
      exact (hle J K h).trans ((pow_le_pow_of_le_one (rad_pos' r).le (rad_lt_one' r).le hJ).trans hJ')
    · exact (hle K J h).trans ((pow_le_pow_of_le_one (rad_pos' r).le (rad_lt_one' r).le hK).trans hJ')
  exact ⟨J₀, fun J hJ K hK => ⟨key _ J hJ K hK, key _ J hJ K hK⟩⟩

def acrisToAnnFun (a : ACris ℂ_[p] p) : (𝓣).Ann ρ0 σ0 := (exists_acrisLimit hσ a).choose

theorem annNorm_acrisToAnnFun_sub_le (a : ACris ℂ_[p] p) {c : ACrisZero ℂ_[p] p} {N : ℕ}
    (hc : a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N})
    (r : AnnRad ρ0 σ0) :
    (𝓣).annNorm ρ0 σ0 r (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (c : 𝔸)) ≤ (r : ℝ) ^ N := by
  set x := acrisToAnnFun hσ a
  have hx := (exists_acrisLimit hσ a).choose_spec r
  have hbound : ∀ J ≥ N, (𝓣).annNorm ρ0 σ0 r (x - awayToAnn ρ0 σ0 (c : 𝔸)) ≤
      max ((𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - x)) ((r : ℝ) ^ N) := by
    intro J hJ
    have e : x - awayToAnn ρ0 σ0 (c : 𝔸) = -(awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - x) +
        (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - awayToAnn ρ0 σ0 (c : 𝔸)) := by ring
    rw [e]
    refine ((𝓣).annNorm_add_le r _ _).trans (max_le_max (by rw [(𝓣).annNorm_neg]) ?_)
    exact annNorm_awayToAnn_sub_le hσ r (sub_mem_span_of_le hJ hc (acrisApprox_spec a J))
  have hlim : Tendsto (fun J => max ((𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - x))
      ((r : ℝ) ^ N)) atTop (𝓝 (max 0 ((r : ℝ) ^ N))) := hx.max tendsto_const_nhds
  rw [max_eq_right (pow_nonneg (rad_pos' r).le N)] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨N, hbound⟩)

theorem annNorm_acrisToAnnFun_le_one (a : ACris ℂ_[p] p) (r : AnnRad ρ0 σ0) :
    (𝓣).annNorm ρ0 σ0 r (acrisToAnnFun hσ a) ≤ 1 := by
  have h1 := annNorm_acrisToAnnFun_sub_le hσ a (acrisApprox_spec a 0) r
  have e : acrisToAnnFun hσ a = (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (acrisApprox a 0 : 𝔸)) +
      awayToAnn ρ0 σ0 (acrisApprox a 0 : 𝔸) := by ring
  rw [e]
  refine ((𝓣).annNorm_add_le r _ _).trans (max_le (h1.trans (by rw [pow_zero])) ?_)
  exact annNorm_awayToAnn_le_one hσ r (acrisApprox a 0).2

theorem eq_acrisToAnnFun {a : ACris ℂ_[p] p} {x : (𝓣).Ann ρ0 σ0}
    (h : ∀ N : ℕ, ∃ c : ACrisZero ℂ_[p] p,
      a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} ∧
      ∀ r : AnnRad ρ0 σ0, (𝓣).annNorm ρ0 σ0 r (x - awayToAnn ρ0 σ0 (c : 𝔸)) ≤ (ρ0 : ℝ) ^ N) :
    x = acrisToAnnFun hσ a := by
  have key : ∀ r : AnnRad ρ0 σ0, (𝓣).annNorm ρ0 σ0 r (x - acrisToAnnFun hσ a) = 0 := by
    intro r
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) ((𝓣).annNorm_nonneg r _)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ρ0.2.2
    obtain ⟨c, hc, hx⟩ := h N
    have e : x - acrisToAnnFun hσ a = (x - awayToAnn ρ0 σ0 (c : 𝔸)) +
        -(acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (c : 𝔸)) := by ring
    rw [e, zero_add]
    refine ((𝓣).annNorm_add_le r _ _).trans (max_le ((hx r).trans hN.le) ?_)
    rw [(𝓣).annNorm_neg]
    exact (annNorm_acrisToAnnFun_sub_le hσ a hc r).trans ((rad_pow_le hσ r N).trans hN.le)
  exact (𝓣).eq_of_annNorm_sub (key _) (key _)

theorem acrisToAnnFun_algebraMap (c : ACrisZero ℂ_[p] p) :
    acrisToAnnFun hσ (algebraMap _ (ACris ℂ_[p] p) c) = awayToAnn ρ0 σ0 (c : 𝔸) :=
  (eq_acrisToAnnFun hσ fun N => ⟨c, by rw [sub_self]; exact Ideal.zero_mem _, fun r => by
    rw [sub_self, (𝓣).annNorm_zero]; exact pow_nonneg ρ0.2.1.le N⟩).symm

def acrisToAnn : ACris ℂ_[p] p →+* (𝓣).Ann ρ0 σ0 where
  toFun := acrisToAnnFun hσ
  map_one' := by
    have := acrisToAnnFun_algebraMap hσ 1
    rwa [map_one, OneMemClass.coe_one, map_one] at this
  map_zero' := by
    have := acrisToAnnFun_algebraMap hσ 0
    rwa [map_zero, ZeroMemClass.coe_zero, map_zero] at this
  map_add' a b := by
    refine (eq_acrisToAnnFun hσ fun N => ⟨acrisApprox a N + acrisApprox b N, ?_, fun r => ?_⟩).symm
    · rw [map_add, add_sub_add_comm]
      exact add_mem (acrisApprox_spec a N) (acrisApprox_spec b N)
    · have e : acrisToAnnFun hσ a + acrisToAnnFun hσ b -
          awayToAnn ρ0 σ0 ((acrisApprox a N + acrisApprox b N : ACrisZero ℂ_[p] p) : 𝔸) =
          (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸)) +
            (acrisToAnnFun hσ b - awayToAnn ρ0 σ0 (acrisApprox b N : 𝔸)) := by
        rw [Subalgebra.coe_add, map_add]; ring
      rw [e]
      exact ((𝓣).annNorm_add_le r _ _).trans (max_le
        ((annNorm_acrisToAnnFun_sub_le hσ a (acrisApprox_spec a N) r).trans (rad_pow_le hσ r N))
        ((annNorm_acrisToAnnFun_sub_le hσ b (acrisApprox_spec b N) r).trans (rad_pow_le hσ r N)))
  map_mul' a b := by
    refine (eq_acrisToAnnFun hσ fun N => ⟨acrisApprox a N * acrisApprox b N, ?_, fun r => ?_⟩).symm
    · have e : a * b - algebraMap _ (ACris ℂ_[p] p) (acrisApprox a N * acrisApprox b N) =
          a * (b - algebraMap _ (ACris ℂ_[p] p) (acrisApprox b N)) +
            (a - algebraMap _ (ACris ℂ_[p] p) (acrisApprox a N)) *
              algebraMap _ (ACris ℂ_[p] p) (acrisApprox b N) := by
        rw [map_mul]; ring
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (acrisApprox_spec b N))
        (Ideal.mul_mem_right _ _ (acrisApprox_spec a N))
    · have e : acrisToAnnFun hσ a * acrisToAnnFun hσ b -
          awayToAnn ρ0 σ0 ((acrisApprox a N * acrisApprox b N : ACrisZero ℂ_[p] p) : 𝔸) =
          acrisToAnnFun hσ a * (acrisToAnnFun hσ b - awayToAnn ρ0 σ0 (acrisApprox b N : 𝔸)) +
            (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸)) *
              awayToAnn ρ0 σ0 (acrisApprox b N : 𝔸) := by
        rw [Subalgebra.coe_mul, map_mul]; ring
      rw [e]
      refine ((𝓣).annNorm_add_le r _ _).trans (max_le ?_ ?_)
      · rw [(𝓣).annNorm_mul]
        refine (mul_le_of_le_one_left ((𝓣).annNorm_nonneg r _)
          (annNorm_acrisToAnnFun_le_one hσ a r)).trans ?_
        exact (annNorm_acrisToAnnFun_sub_le hσ b (acrisApprox_spec b N) r).trans (rad_pow_le hσ r N)
      · rw [(𝓣).annNorm_mul]
        refine (mul_le_of_le_one_right ((𝓣).annNorm_nonneg r _)
          (annNorm_awayToAnn_le_one hσ r (acrisApprox b N).2)).trans ?_
        exact (annNorm_acrisToAnnFun_sub_le hσ a (acrisApprox_spec a N) r).trans (rad_pow_le hσ r N)

theorem acrisToAnn_apply (a : ACris ℂ_[p] p) : acrisToAnn hσ a = acrisToAnnFun hσ a := rfl

end WAFrac

end GroundTheory.PAdicHodge
