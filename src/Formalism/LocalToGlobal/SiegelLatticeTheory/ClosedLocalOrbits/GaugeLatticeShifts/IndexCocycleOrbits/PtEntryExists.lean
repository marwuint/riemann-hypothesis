import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ

noncomputable section

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits.CU

open Formalism.MainNotions.S Matrix

structure Mono {N : ℕ} {K : Type*} [Zero K] (P : Matrix (Fin N) (Fin N) K) : Prop where
  ex : ∀ i, ∃ j, P i j ≠ 0
  row : ∀ i j j', P i j ≠ 0 → P i j' ≠ 0 → j = j'
  col : ∀ i i' j, P i j ≠ 0 → P i' j ≠ 0 → i = i'

end Formalism.L2.SG.Pf.IndexCocycleOrbits.CU
