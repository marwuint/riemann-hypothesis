import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnitaryGroupEveryResidueOfLieStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanks
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_identity_unconditional :
    ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
      (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ :=
  GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie (GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis _root_.GlobalTheory.JR.unitMatch_all).1

end GlobalTheory.UnitLemma
