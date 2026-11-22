import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlocksParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import GroundTheory.AutomorphicForms.FiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 400000 in

theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end CompanionTheory.Pf1.SegRepC.PiLocalization₂

end
