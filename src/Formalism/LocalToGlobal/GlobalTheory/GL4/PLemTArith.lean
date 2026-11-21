import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree

noncomputable section

open NumberField FractionalIdeal
open scoped nonZeroDivisors

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def starO (w : 𝓞 E) : 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E) w

theorem starO_coe (w : 𝓞 E) : ((starO w : 𝓞 E) : E) = star (w : E) := rfl

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
