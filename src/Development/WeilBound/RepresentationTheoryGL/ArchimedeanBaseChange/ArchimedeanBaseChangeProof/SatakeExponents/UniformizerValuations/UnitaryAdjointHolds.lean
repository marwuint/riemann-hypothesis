import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphericalHeckeUnitary.PuSphHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.SphStarUPlug
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHolds

namespace PositivityTheory.Rg.BcB.F.U

theorem unitary_words_holds : UWord :=
  UU.uWordOfU _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg (_root_.GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg) _root_.GlobalTheory.CompanionTheory.CompUnitary.compUnit PositivityTheory.Rg.BcB.F.Fok.sphStarU

theorem unitary_adjoint_holds : UAdj :=
  UU.uAdjOfU _root_.GlobalTheory.CompanionTheory.BlockScalars.diagAlg _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg (_root_.GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne _root_.GlobalTheory.CompanionTheory.LocHecke.locAlg) _root_.GlobalTheory.CompanionTheory.CompUnitary.compUnit PositivityTheory.Rg.BcB.F.Fok.sphStarU

end PositivityTheory.Rg.BcB.F.U
