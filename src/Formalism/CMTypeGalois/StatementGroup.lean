import Mathlib
import Formalism.StatementOC

open Finset

namespace Formalism.Q3

def IsCMTypeG {G : Type*} [Mul G] (c : G) (Φ : Finset G) : Prop := ∀ g : G, g ∈ Φ ↔ c * g ∉ Φ

instance {G : Type*} [Mul G] [Fintype G] [DecidableEq G] (c : G) : DecidablePred (IsCMTypeG c) :=
  fun _ => Fintype.decidableForallFintype

end Formalism.Q3
