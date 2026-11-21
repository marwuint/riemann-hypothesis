import Mathlib

open Finset Real

noncomputable section

namespace Formalism.BehrendSets.Count

def F (n : ℕ) : ℝ := ∑ i ∈ range n, Real.log ((i.factorial : ℕ) : ℝ)

end Formalism.BehrendSets.Count

namespace Formalism.BehrendSets

end Formalism.BehrendSets
