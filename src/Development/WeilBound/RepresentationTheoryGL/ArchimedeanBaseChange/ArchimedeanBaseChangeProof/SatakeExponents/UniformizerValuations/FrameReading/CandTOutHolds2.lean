import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CandOut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandSb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandTb
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandLh
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IsOpenChiMu
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PairDoubleCosetFiniteSupport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.RExpRead
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Imports
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealReadLevi

namespace PositivityTheory.Rg.BcB.F

theorem candTOut_holds2 : CandTOut :=
  candTOut_of (candS_of (Tail.rReadS_c RS.reading_module_holds RS.join_module_holds fun E _ _ _ => PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E))
    (candT_of (Tail.rReadT RS.reading_module_holds) (Tail.rExpRead' N3.Final.n3) RS.joinSat_holds)
    (PCandLh.candLev_of (_root_.GlobalTheory.CompanionTheory.ReadLevel.rReadLev RS.reading_module_holds RS.join_module_holds) (Tail.rReadT RS.reading_module_holds)
      (Tail.rExpRead' N3.Final.n3) RS.joinSat_holds)

end PositivityTheory.Rg.BcB.F
