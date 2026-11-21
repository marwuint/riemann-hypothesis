import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHoldsStatement

namespace GlobalTheory.RgGu.Nup2

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.NuPair k := fun k _ _ _ _ =>
  _root_.GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.T.derivative_jacquet_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (_root_.GlobalTheory.CompanionTheory.JmThetaInv.jmTheta k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (derivSub_main k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)

end GlobalTheory.RgGu.Nup2
