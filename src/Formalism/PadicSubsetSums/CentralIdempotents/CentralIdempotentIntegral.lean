import Mathlib
import Formalism.CyclotomicNorms.StatementTW

open Finset Polynomial Formalism.CyclotomicNorms

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.TW

def relLen {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℕ∞ :=
  Module.length O (↥M ⧸ N.comap M.subtype)

def sIdx {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℤ :=
  ((relLen M N).toNat : ℤ) - ((relLen N M).toNat : ℤ)

end Formalism.IrreducibleCountingLemmas.TW
