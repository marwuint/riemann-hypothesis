import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaValuesVanishAtOddSplitPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmNormalizedThetaJetsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem inp_all : ∀ D, Inp D := fun D =>
  { g1 := (_root_.GlobalTheory.InducedType.induced_type D).1
    perm := (_root_.GlobalTheory.InducedType.induced_type D).2
    uni := _root_.GlobalTheory.theta_translation_intertwiner_unitary D
    mu := GlobalTheory.T.admissible_characters_exist D
    curve := _root_.GlobalTheory.ConjCurve.galCurve_holds D
    gal := _root_.GlobalTheory.GalTheta.gal_all D
    galEx := _root_.GlobalTheory.GalExist.galEx_all D
    t0Ex := _root_.GlobalTheory.TwoTorsionPt.exists_point D
    use1 := _root_.GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D
    alg := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D
    conj := GlobalTheory.T.thetaVacua_conjugates_cmPoints D
    nrm := _root_.GlobalTheory.ConjNorm.useNorm_all D
    bar := GlobalTheory.T.cmTheta_complexConjugation_compatible D
    odd3 := _root_.GlobalTheory.InertSign.vacuum_inert D
    odd4 := _root_.GlobalTheory.VacuumScalar.vacuum_scalar D
    rep := _root_.GlobalTheory.NormSum.exists_rep_trivial_at D
    model := _root_.GlobalTheory.UnitModel.modelEx_holds D
    transl := _root_.GlobalTheory.ThetaTransl.transl_holds D
    two := _root_.GlobalTheory.EvenTheta.atTwo D
    jets := _root_.GlobalTheory.ThetaJets.jetsPh_all D
    split := _root_.GlobalTheory.ThetaSplit.splitZero D
    eqv := GlobalTheory.OddRank.exact_equivariance D }

end GlobalTheory.NormSum
