import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.PrimBase
theorem base_of_ties_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  intro hP D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  have hGiv : GlobalTheory.LiftRows.Given R.toRealDat F.lv2 :=
    GlobalTheory.GivenOfTop.given_of_top R F hT.ok hT.char hT.ex hT.host hT.params hT.ccK hT.guard hT.types
  have hStab : GoodStable A3.A.X := _root_.GlobalTheory.GoodStableGiven.goodStable_of_given hP.q12 R.toRealDat F.lv2 hGiv
  have hCD : GlobalTheory.CuspMult.CuspDecomp D := GlobalTheory.CuspDec.cuspDecomp hP.q3 hP.q2 D
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP.q2 D
  have hCore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : GlobalTheory.Hk3.SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 R.toRealDat
  have hTR : GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF :=
    _root_.GlobalTheory.TrLevMult.trLev_of_multEq R.toRealDat F.lv2 1 hT.ok.ok2 hCore.1 hSch hStab hCD hM R.SF hCore.2.1
  have hFix : ∀ t P, GlobalTheory.Hk3.Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R.toRealDat t P :=
    GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex
  have hU := _root_.GlobalTheory.ScalAll.scal_matchUp_upInj hP.q5 hP.q3 hP.q4 hP.q6 hP.q2 hP.q1 hP.q7 hP.q8
    (_root_.ResidueKilled.sec_of_dm hP.q9) hP.q10 hP.q11 R.toRealDat F.lv2 hGiv hT.ccK
    hT.char.allPl hFix R.SF hCore.2.1 hTR
  exact ⟨hGiv, hStab, hCD, hLI, hTR, hU.2.2.1, hU.2.2.2⟩
end GlobalTheory.PrimBase
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_data_of_multiplicity_one : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  exact @_root_.GlobalTheory.PrimBase.base_of_ties_alt
end
