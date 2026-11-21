import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensHom' : TensHom := by
  exact @GlobalTheory.CompanionTheory.ZuckTensHom.tensHom
