import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfAdmissibility
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll

namespace PositivityTheory.Exh

theorem lUnlinkedIrr_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : GlobalTheory.BZSeg.LUnlinkedIrr k :=
  _root_.GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr k irreducibleAdmissibleGL (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet irreducibleAdmissibleGL hZ) (fun k _ _ _ _ => (geometricLemmaGL k).1)
    (GlobalTheory.CompanionTheory.BZNuPair.nuPair k irreducibleAdmissibleGL) (_root_.GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity k (_root_.GlobalTheory.CompanionTheory.Rodier.whitHeredity k) (PositivityTheory.rg.gu.whit.whitRankIrr k))
    fun _ _ x hd => _root_.GlobalTheory.CompanionTheory.ProdFL.main irreducibleAdmissibleGL x hd

end PositivityTheory.Exh
