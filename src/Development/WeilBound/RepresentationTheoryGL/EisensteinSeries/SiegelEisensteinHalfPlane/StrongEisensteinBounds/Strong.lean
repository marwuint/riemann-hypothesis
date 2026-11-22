import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology

namespace PositivityTheory.Rg.SwEis.Hd

open PositivityTheory.RgEis.Hd

theorem eisStrong : PositivityTheory.Rg.Sw.Glob.EisStrong :=
  _root_.GlobalTheory.CompanionTheory.SwEisTop.eTop dict dictInf (cmGood_of stdGood dict dictInf) grpTop bdetLaw extLaw (parLaw_of bdetLaw extLaw grpTop)
    sgAll _root_.GlobalTheory.CompanionTheory.StdChart.tStd (_root_.GlobalTheory.CompanionTheory.SwEisIwa.eIwa (_root_.GlobalTheory.CompanionTheory.TChartProof.tChart dict dictInf _root_.GlobalTheory.CompanionTheory.StdChart.tStd)) (_root_.GlobalTheory.CompanionTheory.ScalWall.tScal secLaw (wallLaw_of secLaw))
    (_root_.GlobalTheory.CompanionTheory.FarSeries.eFar htLip) _root_.GlobalTheory.CompanionTheory.PolyDenominator.glue

end PositivityTheory.Rg.SwEis.Hd
