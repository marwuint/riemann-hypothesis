import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsBijectiveOfParts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftScalarIdentityMatchingAdjointInjective
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GUnitOfModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PGEquivOfBaseW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTheoremAPublishedHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftSecondHypotheses
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefinitePositivityBothLevelsShortList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPositiveScalarsBasePlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesLiftData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesUnitEquiv
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage2
theorem stage2_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) ∧ (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) ∧ R.PrincipalLevelBijective F := by
  intro P eps heps
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := _root_.ResidueKilled.sec_of_dm P.q9
  obtain ⟨x₀, hx₀⟩ := _root_.GlobalTheory.PosShort.pos_short P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q12 eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F L hLe hLx hSz hPar hT hM hRow
  obtain ⟨pV⟩ := hPar
  obtain ⟨_hGiven, _hGS, _hCD, _hLI, hTR, hUI, _hUIW⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  obtain ⟨_hOk, _hGU, hGE, hBlk, _hA, _hB⟩ := _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hPos : ∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos :=
    hx₀ (s := 1) R F L pV hLe hLx hSz hT.ok hT.char hT.ex hT.host hT.ccK hT.guard hT.types hTR hGE hBlk hRow
  have hScal := _root_.GlobalTheory.PosScalBase.pos_scal_base P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hTR hJ hGE hPos
  exact ⟨hPos, hScal, GlobalTheory.PrimIn.principalLevel_rows_bijective_of_parts R F hT.ok hT.char hUI hRow hBlk⟩
end GlobalTheory.Stage2
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_bijective_of_multEq : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) ∧ (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) ∧ R.PrincipalLevelBijective F := by
  exact @_root_.GlobalTheory.Stage2.stage2_alt
end
