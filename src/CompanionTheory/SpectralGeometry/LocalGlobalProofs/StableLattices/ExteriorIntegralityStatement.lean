import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExteriorIntegrality : WedgeInt := by
  exact @GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt
