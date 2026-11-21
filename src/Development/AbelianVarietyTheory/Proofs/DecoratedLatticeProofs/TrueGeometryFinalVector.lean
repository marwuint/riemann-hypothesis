import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeForward
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeImage
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeKernel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDual
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMatrixEntryIntegralOfKeepsStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCompactLevelProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryIntegralityCongruence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalRelation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalProperty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMatrixMemLevelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.FamTraceChiCol

open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain in

theorem conj_embX_toBlocks₂₂ {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((typeFrame ϖ ord).bas⁻¹ * embX c g * (typeFrame ϖ ord).bas).val.toBlocks₂₂ = 1 := by
  have e1 : (typeFrame ϖ ord).bas.val = fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val := rfl
  have e2 : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val := by
    change (embA n _)⁻¹.val = _
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, show (embX c g).val = fromBlocks g.val 0 0 1 from rfl,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Units.inv_mul]

end GlobalTheory.FamTraceChiCol

namespace GlobalTheory.FamTraceChiCol

end GlobalTheory.FamTraceChiCol
