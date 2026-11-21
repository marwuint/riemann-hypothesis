import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEdge
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelZeroStabilizerMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOfSupportedAtOrthogonalSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNEmbXInvMulMemKOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFrameEmbeddingLocalElementEqEmbeddedMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramAtOfUnramOutside

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceMatch

theorem mem_GfC_of_suppAt' {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V}
    (hg : Formalism.L2.Theta.SuppAt e V g) : g ∈ GfC V := by
  obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem suppAt_conj' {D : D7} {e : Formalism.L2.Theta.AE D} {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) (t : GA D V) :
    Formalism.L2.Theta.SuppAt e V (t⁻¹ * g * t) := by
  refine GlobalTheory.LocGrp.suppAt_of_sandwich hg (mt V t⁻¹) (mt V t) ?_
  rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.MixModel.mt_inv_mul]

end GlobalTheory.PlaceMatch

