import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionCommuteOfFixesIsotropicColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeMulOfUnipotentCoverDiscreteSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicUnipotentRadicalCoveredByLeviConjugates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFixatorEqUnipotentRadicalMulCommonFixator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFixatorOfColumnsIsSemidirectLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCompactInterUnitaryRationalPoints
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_ratPts_fixG_tor_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ B : ℝ, ∀ (μ : Fin j → ℕ) (T : Finset (GAd σ J)), (∀ t ∈ T, t ∈ ratPts σ J) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ fixG σ J C → t = t') → (∀ t ∈ T, ∃ q ∈ fixG σ J C, ∃ w ∈ W, t = q * lv (tor F E fun i => (μ i : ℤ)) * w) → (T.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  obtain ⟨-, hQc, -, -, hNQ, hQP, -, hnorm, hpar⟩ := GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties F E σ n J j m C D Z J₀ hF
  obtain ⟨V, B₁, hV, hcov⟩ := _root_.GlobalTheory.SphEis.cover_unipRad F E σ n J j m C D Z J₀ hF lv hlv
  obtain ⟨ν, π, DN, DM, hSL⟩ := _root_.GlobalTheory.SphEis.semiLat_fixG F E σ n J j m C D Z J₀ hF
  let Λ : Subgroup (GAd σ J) := ratPts σ J ⊓ fixG σ J C
  haveI : DiscreteTopology Λ := inferInstance
  haveI : Countable Λ := inferInstance
  have hDom := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Λ (Measure.haar : Measure (GAd σ J))
  obtain ⟨B, hB0, hB⟩ := _root_.GlobalTheory.SphEis.card_le_mul_of_unip_cover (GAd σ J) (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D) Λ (ratPts σ J) (fixG σ J C)
    ν π DN DM Measure.haar _ V W hSL inf_le_left inf_le_right hQc
    (fun q hq => by
      obtain ⟨u, hu, x, hx, e, -⟩ := _root_.GlobalTheory.SphEis.fixG_eq_unipRad_mul F E σ n J j m C D Z J₀ hF q hq
      exact ⟨u, hu, x, hx, e⟩)
    (fun K hK => _root_.GlobalTheory.SphEis.compact_inter_ratPts_finite F E σ n J K hK) inferInstance hDom hV hW
  refine ⟨B * B₁, fun μ T hT hdist hform => ?_⟩
  set a := lv (tor F E fun i => (μ i : ℤ)) with ha
  obtain ⟨Y, hYc, hYN, hYcov⟩ := hcov μ
  have haP : a ∈ parFlag σ J C (fun _ => 0) := hpar a _ (hlv.onC _)
  have h1 := hB a Y T
    (fun x hx => (_root_.GlobalTheory.SphEis.lv_comm_of_fix_cols F E σ n J j m C D Z J₀ hF lv hlv _ x hx))
    (fun u => by
      have := hnorm a⁻¹ (inv_mem haP) u
      simpa only [inv_inv] using this)
    hYN
    (fun u hu => by
      obtain ⟨γ, hγ, hγN, y, hy, w, hw, -, e⟩ := hYcov u hu
      exact ⟨γ, ⟨hγ, hNQ hγN⟩, hγN, y, hy, w, hw, e⟩)
    hT
    (fun t ht t' ht' h => hdist t ht t' ht' h.2)
    hform
  calc (T.card : ℝ) ≤ B * Y.card := h1
    _ ≤ B * (B₁ * ∏ i, bse F ^ ((m + j) * μ i)) := mul_le_mul_of_nonneg_left hYc hB0
    _ = B * B₁ * ∏ i, bse F ^ ((m + j) * μ i) := by ring

end GlobalTheory.SphEis
