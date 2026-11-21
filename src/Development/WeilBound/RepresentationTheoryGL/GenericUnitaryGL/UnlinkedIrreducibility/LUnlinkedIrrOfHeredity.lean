import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerRankHeredity.ProdFL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdQuotGenericOfStdSubGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairIrreducibleUnlinked
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiProdCompInvTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import BuildAid.D3
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

noncomputable section

namespace GlobalTheory.RgGu.Unl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem whitRankStd : GlobalTheory.BZSeg.WhitRankStd k :=
  _root_.GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity k (_root_.GlobalTheory.CompanionTheory.Rodier.whitHeredity k) (PositivityTheory.rg.gu.whit.whitRankIrr k)

theorem lUnlinkedIrr_nu (hJ : Zc.LSegJacquet k) (hG : GlobalTheory.Published.GeometricLemmaFiltration) (hN : GlobalTheory.BZSeg.NuPair k) :
    GlobalTheory.BZSeg.LUnlinkedIrr k := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := by
    first
    | exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    | exact PositivityTheory.Exh.irreducibleAdmissibleGL
    | exact GlobalTheory.RgGu.irreducibleAdmissibleGL
  have hF : GlobalTheory.BZSeg.ProdIrrFiniteLength k := by
    first
    | exact GlobalTheory.RgGu.prodIrrFiniteLength k
    | exact fun h N x hd => GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  exact _root_.GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr k hA hJ hG hN (whitRankStd k) hF

theorem lUnlinkedComm_of_irr (hL : GlobalTheory.BZSeg.LUnlinkedIrr k) : GlobalTheory.BZSeg.LUnlinkedComm k :=
  GlobalTheory.T.unlinked_commute_of_irreducible k GlobalTheory.RgGu.irreducibleAdmissibleGL hL

end GlobalTheory.RgGu.Unl

end
