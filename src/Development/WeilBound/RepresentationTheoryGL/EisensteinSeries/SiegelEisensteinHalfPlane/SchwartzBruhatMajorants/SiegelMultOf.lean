import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ContinuousOnThetaCFunLtr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.MirGen
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SgOneHd
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHolds
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLaws
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroup
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGalleryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativityStatement
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic

noncomputable section

namespace PositivityTheory.RgEis.Hd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem idTube : IdTube := _root_.GlobalTheory.CompanionTheory.Eis.idTube
theorem tubeChain : TubeChain := _root_.GlobalTheory.CompanionTheory.TubeFourier.tubeChain
theorem secLaw : SecLaw := GlobalTheory.T.section_law_holds
theorem htLip : HtLip := _root_.GlobalTheory.CompanionTheory.RgEis.htLip
theorem stage : PiLocalization₂ := GlobalTheory.T.staged_estimate_holds
theorem wallLaw_of : SecLaw → WallLaw := _root_.GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw
theorem cross_of : SecLaw → HtLip → PiLocalization₂ → WallLaw → Cross := GlobalTheory.T.crossing_of_walls_and_heights
theorem gallery_of : SecLaw → IdTube → TubeChain → Cross → Gallery := _root_.GlobalTheory.CompanionTheory.RgEisGal.gallery
theorem transfer_of : SecLaw → WallLaw → Transfer := _root_.GlobalTheory.CompanionTheory.RgTransfer.transfer
theorem twist_of : SecLaw → Twist := GlobalTheory.T.twist_of_section_law
theorem scale : Scale := GlobalTheory.T.eisenstein_scaling_law
theorem grpTop : GrpTop := _root_.GlobalTheory.CompanionTheory.RgEisTop.grpTop
theorem bdetLaw : BdetLaw := GlobalTheory.T.block_determinant_law
theorem extLaw : ExtLaw := GlobalTheory.T.extension_law
theorem parLaw_of : BdetLaw → ExtLaw → GrpTop → ParLaw := GlobalTheory.T.parabolic_law_of_block_det
theorem leviS_of : BdetLaw → ExtLaw → GrpTop → LeviS := GlobalTheory.T.levi_decomp_of_block_det
theorem leviQ_of : BdetLaw → ExtLaw → GrpTop → LeviQ := _root_.GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ
theorem convGrOf_of : BdetLaw → ExtLaw → ConvGrOf := _root_.GlobalTheory.CompanionTheory.Plucker.convGrOf
theorem convU_of : ParLaw → ConvU := GlobalTheory.T.unipotent_convergence_of_parabolic
theorem sgStep_of : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := GlobalTheory.T.siegel_induction_from_gallery
theorem epConv : EpConv := GlobalTheory.CompanionTheory.EpConvB.epConv
theorem epMain_of : EpConv → EpMain := GlobalTheory.CompanionTheory.EpsteinMain.Hd.epMain_of_epConv
theorem testFun : TestFun := PositivityTheory.RgEis.TF.testFun
theorem testSph : TestSph := GlobalTheory.T.spherical_test_function_exists
theorem stdGood : StdGood := _root_.GlobalTheory.CompanionTheory.StdGoodAd.stdGood
theorem mirGen_of : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen := PositivityTheory.RgEis.MG.mirGen
theorem dict : Dict := GlobalTheory.T.local_global_dictionary
theorem dictInf : DictInf := GlobalTheory.T.archimedean_local_global_dictionary
theorem cmGood_of : StdGood → Dict → DictInf → CMGood := _root_.GlobalTheory.CompanionTheory.RgEisCM.cmGood
theorem cmMir_of : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := GlobalTheory.T.constant_multiplier_mirabolic
theorem sgOne_of : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := PositivityTheory.RgEis.So.sgOne_hd
theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := GlobalTheory.T.siegel_eisenstein_multiplicativity

theorem sgAll_of (hG : CMGood) (hM : CMMir) (h1 : SgOne) (hS : SgStep) : SgAll := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε
  suffices H : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → 1 ≤ n → (adCM σ χ).Sg ε ι from
    fun ι _ _ hι => H _ ι rfl hι
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hι hn
    rcases Nat.eq_or_lt_of_le hn with e | e
    · exact h1 F E σ χ c h h' hχ hc ε ι (hι.trans e.symm)
    · exact hS E _ (adCM σ χ) (hG F E σ χ c h h' hχ hc) (hM F E σ χ c h h' hχ hc) ε ι (by omega)
        fun κ _ _ h1 h2 => ih _ (hι ▸ h2) κ rfl h1

theorem sgAll : SgAll :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
    (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
    (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
      (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
      (convGrOf_of bdetLaw extLaw) (convU_of hP))

theorem eisBL : GlobalTheory.ThK.Dbl.EisBL :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  SiegelEisensteinSeries.BRoad.eisBL_of _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf
    (siegelMult_of secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation

end PositivityTheory.RgEis.Hd
