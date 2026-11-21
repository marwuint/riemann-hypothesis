import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  exact @GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective
