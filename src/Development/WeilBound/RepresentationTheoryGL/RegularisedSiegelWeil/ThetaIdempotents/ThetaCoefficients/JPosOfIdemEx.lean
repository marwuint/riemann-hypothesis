import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponents
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.GoodPlacesOutsideFiniteSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompactBis

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

theorem jPos_of_idemEx : IdemEx → JPos := by
  intro _ D n r t hrt hr ψ hψ χ hχ hres nb hnb S
  have hB2 : SplitPlaceRankCutEigenvalue := _root_.GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation (_root_.GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps _root_.GlobalTheory.CompanionTheory.Jp.Iw.jpIw GlobalTheory.T.height_bound_statement _root_.GlobalTheory.CompanionTheory.Jp.Unif.jpUnif _root_.GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp _root_.GlobalTheory.CompanionTheory.Jp.Pos.jpPos)
  obtain ⟨v, hvS, hpsi, τ, hchi⟩ := _root_.PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound D r ψ hψ χ hχ hres S
  obtain ⟨C, c, hK, hd, hc, hint⟩ := hB2 D n r t hrt hr ψ hψ nb hnb v hpsi τ
  refine ⟨v, hvS, C, c, hK, hd, hc, ?_⟩
  intro νv hH hP z f _ hlaw hinv g
  exact GlobalTheory.T.section_eigenfunction_maximal_compact D n χ nb hnb v τ hchi C νv hH z (c z) (hint νv hH hP z) f hlaw hinv g

end GlobalTheory.CompanionTheory.Jp
