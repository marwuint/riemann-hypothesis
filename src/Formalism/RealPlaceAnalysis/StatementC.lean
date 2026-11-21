import Formalism.RealPlaceAnalysis.StatementB

open Finset

noncomputable section

namespace Formalism.REAL

def cyc {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W}

def chamber {n : ℕ} (G : Fin n → Fin n → ℤ) : Set (Fin n → ℤ) :=
  {m | ∀ a b, a < b → G a b ≤ m a - m b}

end Formalism.REAL
