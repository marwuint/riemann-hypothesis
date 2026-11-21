import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ToRawComplex : ToRaw := by
  exact @GlobalTheory.CompanionTheory.ZuckToRaw.toRaw
