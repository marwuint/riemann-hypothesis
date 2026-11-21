import Mathlib

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.A

def mfact {σ : Type*} (g : σ →₀ ℕ) : ℕ := g.prod fun _ n => n.factorial

end Formalism.A
