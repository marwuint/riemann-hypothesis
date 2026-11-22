import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Mathlib

section
namespace ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim
namespace CompanionTheory.Member.ThetaDownProjection
end CompanionTheory.Member.ThetaDownProjection
theorem CompanionTheory.Member.twisted_period_identity_local : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := by
  intro hP
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ t x hx
  rw [← ch.cv.thDn_w s.core.chain]
  exact CompanionTheory.Member.ThetaDownProjection.proj_thDn hP.cuspRapidDecay s.core t x hx _
end
end ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.twisted_period_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local
end
end

section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_period_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → StepProj := ThetaProjectionIdempotent.CompanionTheory.Member.twisted_period_identity_local
end
