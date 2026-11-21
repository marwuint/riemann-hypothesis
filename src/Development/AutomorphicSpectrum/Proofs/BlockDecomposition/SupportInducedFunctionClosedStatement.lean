import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportInducedFunctionClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_induced_function_closed : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q : Subgroup G} (σ : Representation ℂ Q W₁) (f : smoothPart (ind Q σ)), IsClosed {g : G | f.1.1 g ≠ 0} := by
  exact @GlobalTheory.CompanionTheory.BZRes.isClosed_support_smooth_ind
