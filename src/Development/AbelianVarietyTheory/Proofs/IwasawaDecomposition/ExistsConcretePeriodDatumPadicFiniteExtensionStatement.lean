import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcretePeriodDatumPadicFiniteExtension
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_concretePeriodDatum_padicFiniteExtension : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l), ∃ PD, IsRealPD C K PD := by
  exact @GlobalTheory.MemLoc.PdEx.exists_realPD
