import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_phi_minus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.SmPhiMinus k := by
  exact @GlobalTheory.CompanionTheory.BZMirSmooth.smPhiMinus
