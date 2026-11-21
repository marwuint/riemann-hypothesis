import Mathlib
import Formalism.FormalDegreeBessel.StatementDS

open Finset
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords

open Formalism.QuantumDeterminants

def comb {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (j : A → V) (μ : A) (a : A →₀ ℂ) : V :=
  ∑ ν ∈ a.support, a ν • j (μ + ν)

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
