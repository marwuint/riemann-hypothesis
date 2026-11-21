import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfAdmissibility
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement

namespace PositivityTheory.Exh

theorem lUnlinkedIrr_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : GlobalTheory.BZSeg.LUnlinkedIrr k :=
  _root_.GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr k irreducibleAdmissibleGL (GlobalTheory.T.segment_jacquet_all irreducibleAdmissibleGL hZ) (fun k _ _ _ _ => (geometricLemmaGL k).1)
    (GlobalTheory.CompanionTheory.BZNuPair.nuPair k irreducibleAdmissibleGL) (_root_.GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity k (_root_.GlobalTheory.CompanionTheory.Rodier.whitHeredity k) (PositivityTheory.rg.gu.whit.whitRankIrr k))
    fun _ _ x hd => _root_.GlobalTheory.CompanionTheory.ProdFL.main irreducibleAdmissibleGL x hd

end PositivityTheory.Exh
