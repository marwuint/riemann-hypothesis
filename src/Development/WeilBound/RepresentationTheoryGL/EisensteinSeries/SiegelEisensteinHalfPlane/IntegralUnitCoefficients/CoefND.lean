import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCoefficientOfConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNondegenerateOfIwasawa
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditivity
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SphericalBigCell.IfrBAddOfWeilThetaConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealMatch
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.SwmConeHaar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneral
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop2
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top7
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitGenLt
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MatchMono
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.Bridge
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WlocTop
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.GenAHf

noncomputable section

namespace PositivityTheory.SiegelWeilCoefficients

open PositivityTheory.Rg.Sw.Glob PositivityTheory.PfSWUS

theorem coefND : CoefND :=
  _root_.GlobalTheory.CompanionTheory.SWGlue.ndOfWhit _root_.GlobalTheory.CompanionTheory.SwUnf.unfold (_root_.GlobalTheory.CompanionTheory.ThetaCoefND.thetaCoef wtc)
    (_root_.GlobalTheory.CompanionTheory.IwaAd.iwaRedA (_root_.GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt whitGenLt (_root_.GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts _root_.GlobalTheory.CompanionTheory.PfSWUS.fockSplitK _root_.GlobalTheory.CompanionTheory.WhitAdd.whitTAdd
      (PositivityTheory.PfSWUS.HandIAdd.ifrBAdd_of_weilThetaConvergence wtc) PositivityTheory.PfSWUS.SwMatch.matchMono)
      _root_.GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange))

theorem lit : GlobalTheory.Published.SiegelWeilUnitarySchrodingerLit := by
  intro D n V a1 a2 a3 ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω H hH l hl s hs ν hν Φ hΦ g
  exact top7 genA_hf (gIdil_gen wtc genA_hf) coefND D n V ψ χ θ μ ω H l s ν Φ
    ⟨hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω, hH, hl, hs, hν, hΦ⟩ ⟨a1, a2, a3⟩ (by omega) g

theorem field : GlobalTheory.Published.SiegelWeilUnitarySchrodinger :=
  PositivityTheory.Lit1.SWUS.siegelWeilUnitarySchrodinger_of_lit lit wtc

end PositivityTheory.SiegelWeilCoefficients

end
