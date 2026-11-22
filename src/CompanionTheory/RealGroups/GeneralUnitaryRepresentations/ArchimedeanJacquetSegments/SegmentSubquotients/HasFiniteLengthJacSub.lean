import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.SegTwo

def RhoNuRhoReducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def revTensor {d : ℕ} (σ : IrrRep (GL (Fin d) k)) :=
  piTensor fun a : Fin 2 => segTerm σ.ρ 2 a.rev

end CompanionTheory.Pf1.SegRepC.SegTwo

end
