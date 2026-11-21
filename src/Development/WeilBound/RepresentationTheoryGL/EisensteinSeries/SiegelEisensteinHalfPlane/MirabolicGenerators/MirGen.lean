import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := GlobalTheory.T.side_term_identity hG hB
    have hZ := GlobalTheory.T.zeta_integral_of_epstein_conv hC
    _root_.GlobalTheory.CompanionTheory.EisMir.mirGen_of_core hS hSph _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem (_root_.GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) hO (_root_.GlobalTheory.CompanionTheory.EisTestK.testK hG hB hT)
      (_root_.GlobalTheory.CompanionTheory.EisCore.wall_core hM _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood (_root_.GlobalTheory.CompanionTheory.RgEisMG.master _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem _root_.GlobalTheory.CompanionTheory.RgEisDGood.dGood _root_.GlobalTheory.CompanionTheory.RgEisHGood.hGood _root_.GlobalTheory.CompanionTheory.RgEisLeft.bGood) hO _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ
        (GlobalTheory.T.side_term_unfolding hC (_root_.GlobalTheory.CompanionTheory.RgEisUnfold.unfold hS _root_.GlobalTheory.CompanionTheory.EisMirGen.avgMem) GlobalTheory.T.lines_decomposition _root_.GlobalTheory.CompanionTheory.RgEisTerm.term hZ) (GlobalTheory.T.side_term_convergence hC hSph GlobalTheory.T.lines_decomposition _root_.GlobalTheory.CompanionTheory.RgEisTerm.term) (GlobalTheory.T.zeta_value_at_one hM))

end PositivityTheory.RgEis.MG
