import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPeriod
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.Separate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingModelsOfSeparatingData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyExtendsByTwistedRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSeesawPairOfThetaData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConvergenceOfSeparatingFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCoreSurjectiveOfLocalComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RapidDecayOfSeparatingFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselSeparate

section
namespace UpperTheory.Lit
theorem real_functionals_separate_of_hypothesis
    (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := _root_.GlobalTheory.T.exists_models_of_separating_data P
  have rowStep := _root_.GlobalTheory.T.separating_family_extend_by_twist P (_root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data P) rowModels
  have rowTower := _root_.GlobalTheory.SepRows.rowTower_of_step rowModels rowStep
  have conv := _root_.GlobalTheory.T.convergence_of_separating_family P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := _root_.GlobalTheory.T.twist_core_surjective P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := _root_.GlobalTheory.SepRows.weakSep_of_steps _root_.GlobalTheory.SepRows.sizeGap_of_sizes (_root_.GlobalTheory.T.exists_separating_models P) (_root_.GlobalTheory.T.rapid_decay_of_separating_family P rowTower) per onto
    (_root_.GlobalTheory.Asc.ascent_of_depFixed _root_.GlobalTheory.DepthFix.depFixed)
  exact _root_.UpperTheory.Lit.bessel_separate_of_step_gap P rowTower _root_.GlobalTheory.SepRows.sizeGap_of_sizes _root_.GlobalTheory.SepRows.goodRows conv weak
end UpperTheory.Lit
end
