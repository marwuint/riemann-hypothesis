import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImPosScaledUpperHalfPlane
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootOfUnityCharacterPeriodic
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.ScalarIntegralEstimates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumConjugation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NeZeroOfRePos
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentsTransferOneOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.B1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeGaussLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnTranslateFd
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.SecondDifferenceCpowBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountEqCardZmod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountOfNotDvdJacobi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareEuler
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyFactorCoeffZeroValuationEqProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumFloorHalf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierIntegrationByParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierContinuationDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOneAddSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCuspZeroFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfIntegralEisensteinContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphyIntegralParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldedIdentityOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdUniformizerEqOne
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasProdMoebiusConvOfNormLe

namespace Ad3.S

theorem t1 : T1 := (@GlobalTheory.CompanionTheory.HalfTheta.t1 : T1)

theorem t2 : T2 := (@GlobalTheory.CompanionTheory.HalfWeight.finite_sum_splitting : T2)

theorem t3 : T3 := (@Ad3.S.third_estimate_of_first_two : T1 → T2 → T3) t1 t2

theorem t4 : T4 := (@GlobalTheory.CompanionTheory.HalfWeight.gauss_sum_conjugation : T4)

theorem t5 : T5 := (@GlobalTheory.CompanionTheory.HalfWeightUnfold.term_of_theta : T3 → T4 → T5) t3 t4

theorem u1 : U1 := (@GlobalTheory.CompanionTheory.Unfolding.unfolding_strip : U1)

theorem b1 : B1 := (@GlobalTheory.CompanionTheory.CuspDecay.b1 : B1)

theorem b2 : B2 := (@GlobalTheory.CompanionTheory.ThetaBound.b2 : B2)

theorem u2a : HorizontalIntegralTwisted := (@GlobalTheory.CompanionTheory.HalfIntegralWeight.unfolding_of_bound : B2 → HorizontalIntegralTwisted) b2

theorem u2 : U2 := (@GlobalTheory.CompanionTheory.HalfWt.strip_integral : B1 → B2 → HorizontalIntegralTwisted → U2) b1 b2 u2a

theorem d1 : D1 := (@GlobalTheory.CompanionTheory.CuspHeight.integrableOn_translate_fd : D1)

theorem lB : LB := (@Ad3.S.lB_of : LB)

theorem n1 : N1 := (@GlobalTheory.CompanionTheory.SquareRootCount.rr_eq : N1)

theorem n2 : N2 := (@GlobalTheory.CompanionTheory.SqrtCount.countingSquareRoots : N2)

theorem a2 : A2 := (@GlobalTheory.CompanionTheory.SquareEuler.euler_coeff : N1 → N2 → A2) n1 n2

theorem a1 : A1 := (@GlobalTheory.CompanionTheory.HalfInt.charpoly_factor_coeff_zero_valuation_eq_prod : LB → N2 → A2 → A1) lB n2 a2

theorem a0 : A0 := (@GlobalTheory.CompanionTheory.HalfIntZero.main : LB → N2 → A2 → A0) lB n2 a2

theorem w0 : W0 := (@GlobalTheory.CompanionTheory.HalfWeight.w0 : W0)

theorem w1 : W1 := (@GlobalTheory.CompanionTheory.HalfIntegral.kernel_fourier_integration_by_parts : W0 → W1) w0

theorem w2 : W2 := (@GlobalTheory.CompanionTheory.HalfWeight.kernel_fourier_continuation_decay : W0 → W1 → W2) w0 w1

theorem p1 : P1 := (@GlobalTheory.CompanionTheory.HalfWeightKernel.poisson_kernel : W0 → W2 → P1) w0 w2

theorem p2 : P2 := (@GlobalTheory.CompanionTheory.EisensteinPoissonSummation.eisenstein_cusp_zero_fourier_expansion : P1 → P2) p1

theorem e0 : E0 := (@GlobalTheory.CompanionTheory.HalfInt.half_integral_eisenstein_continuation : A0 → A1 → W0 → W1 → W2 → P2 → E0) a0 a1 w0 w1 w2 p2

theorem g0 : G0 := (@GlobalTheory.CompanionTheory.InvGammaStrip.g0 : G0)

theorem hI : HI := (@GlobalTheory.CompanionTheory.RgAds.holomorphy_integral_param : HI)

theorem s1 : S1 := (@GlobalTheory.CompanionTheory.HalfWeight.unfolded_identity_of : T5 → U1 → U2 → B2 → S1) t5 u1 u2 b2

theorem e1 : E1 := (@GlobalTheory.CompanionTheory.HalfIntegral.e1 : E1)

end Ad3.S
