import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealData
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
namespace GlobalTheory.LowRowAdel
theorem adelC_of_siegelWeil_of_doubling_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  intro hCusp hWS _hSWc hDbl hUnr hBZ hFD D G _ _ Pl0 T A Ks _ _ _ R F hL hStd
  have hHM : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule :=
    GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hLoc : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock := GlobalTheory.SingleBlock.localIntegralSingleBlock
  have hPM : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.T.adelicLift_scalar_of_innerProductFormula R F (_root_.GlobalTheory.LowRow.CuspLift.liftIsCuspC hCusp R F) (_root_.GlobalTheory.SourceLaw.sourceLevelLaw hLoc R F hPM)
    (_root_.GlobalTheory.innerProductFormula_of_hypotheses hCusp hWS (_root_.ResidueKilled.sec_of_dm hDbl) R F hL)
    (_root_.GlobalTheory.FockCoeffImage.fockCoefficientC hHM R F hPM) (deltaNorm_all D)
    (_root_.GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL R F (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUnr R F)) (_root_.GlobalTheory.LevelIndex.levelIndexNormC hLoc R F hPM)
    (GlobalTheory.T.unitaryMassLowerBound_of_orthonormalLatticeFrames D hStd) (_root_.GlobalTheory.LowRow.formalDegreeUpperC_of_hypotheses hFD R F)
end GlobalTheory.LowRowAdel
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  exact @_root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt
end
