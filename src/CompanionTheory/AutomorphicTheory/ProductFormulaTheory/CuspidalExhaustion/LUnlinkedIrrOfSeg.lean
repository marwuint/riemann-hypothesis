import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.IrreducibleAdmissibleGL
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.WhitCuspOfSegCuspGeneric
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfAdmissibility
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll

namespace CompanionTheory.Exh

theorem lUnlinkedIrr_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : GlobalTheory.BZSeg.LUnlinkedIrr k :=
  _root_.GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr k irreducibleAdmissibleGL (_root_.GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet irreducibleAdmissibleGL hZ) (fun k _ _ _ _ => (geometricLemmaGL k).1)
    (GlobalTheory.CompanionTheory.BZNuPair.nuPair k irreducibleAdmissibleGL) (_root_.GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity k (_root_.GlobalTheory.CompanionTheory.Rodier.whitHeredity k) (CompanionTheory.rg.gu.whit.whitRankIrr k))
    fun _ _ x hd => _root_.GlobalTheory.CompanionTheory.ProdFL.main irreducibleAdmissibleGL x hd

end CompanionTheory.Exh
