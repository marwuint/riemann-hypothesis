import Formalism.FrobeniusOrbits.Statement

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def KinE {L : Type*} [Field L] [Algebra ℚ L] (ζ a b : L) : IntermediateField ℚ (hostE ζ a b) :=
  ℚ⟮bE ζ a b⟯

def HostDiffSupport : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime →
    P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) →
      ((2 : ℤ) : 𝓞 (hostE ζ a b)) ∈ P ∨ ((q : ℤ) : 𝓞 (hostE ζ a b)) ∈ P

end Formalism.FrobeniusOrbits
