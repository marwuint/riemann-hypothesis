import Mathlib
import Formalism.FlagUnipotentLattices.DetIndexProductPlacesInequalitySq

open Module NumberField nonZeroDivisors Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def UnitsSquareIndex : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], (∀ w : InfinitePlace F, w.IsReal) →
    Nat.card ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range) = 2 ^ finrank ℚ F

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
