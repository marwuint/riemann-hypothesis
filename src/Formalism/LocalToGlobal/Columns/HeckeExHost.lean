import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeEx
import Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

namespace HeckeExHost

open Formalism.L2.Host Formalism.L2.Host.CharEx Formalism.L2.Col.HeckeEx Formalism.L2.DIV
open scoped Pointwise

section Gen

variable {X : Fields}

theorem conjO_conjO' (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show starRingEnd X.E (starRingEnd X.E (x : X.E)) = (x : X.E)
  simp

def conjPrime₂ (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO']
      exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    have := congrArg X.conjO this
    rwa [conjO_conjO', map_zero] at this

end Gen

end HeckeExHost

end Formalism.L2.Col
