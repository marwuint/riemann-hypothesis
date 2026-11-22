import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.OfDat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoverFieldOfWeberLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LUnifAtDat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatLIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimRows3OfParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanish
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeNZOfNonVanGen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjWOfAForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftScalarIdentityMatchingAdjointInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GUnitOfModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PGEquivOfBaseW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTheoremAPublishedHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftSecondHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsBijectiveOfParts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefinitePositivityBothLevelsShortList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPositiveScalarsBasePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibility
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeClose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateBaseLevelOfHoweUnramifiedCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarPosAllPlacesOfConjugateIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormNormEqAtConjugateEmbedding

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.AtDatumEvaluation

open GlobalTheory.Mem.Top.GroupRetwisting

theorem ev_scale {p : ℝ → ℝ → Prop} (h : ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, p eps x₀) :
    Ev fun K => ∃ x₀ : ℝ, x₀ ≤ K.s.x ∧ p K.s.eps x₀ :=
  ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    let ⟨x₀, hx⟩ := h eps h0
    ⟨x₀, fun _ _ _ _ hs hx' => ⟨x₀, hx', hs ▸ hx⟩⟩⟩⟩⟩⟩

theorem serClause_of_typesTrue (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) {P : Formalism.L2.Host.PiBar D.host} {W : Formalism.L2.Host.Omg D.host}
    (hT : TypesTrue D.ntypes P W) : SerClause D := by
  intro k
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hζ : Formalism.L2.NT.IsGenSys (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro d hd
    refine ⟨(GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order d hd, fun d' hdd hd' => ?_⟩
    obtain ⟨e, rfl⟩ := hdd
    exact (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_norm d e hd (Nat.pos_of_mul_pos_left hd')
  obtain ⟨O, -, -, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
    (_root_.GlobalTheory.GreenParam.cuspParam_of_green hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen hζ)
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact ⟨_, O, fun f => (hT.ser k f).trans (_root_.GlobalTheory.SerCmp.eSerC_eq_eSerO hG _ _ _ _ _ (hT.teich k) O hO D.R.r f hr)⟩

end GlobalTheory.Mem.R3.Rw.AtDatumEvaluation

end
