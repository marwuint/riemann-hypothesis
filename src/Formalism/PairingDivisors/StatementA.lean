import Mathlib
import Formalism.PairingDivisors.StatementH

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def eq {k : Type} [Field k] (q : ℕ) (s : ℕ) (Y : k) : k :=
  (1 - Y * ((q : k) ^ s)⁻¹) * (1 - Y⁻¹ * ((q : k) ^ s)⁻¹) + ((q : k) - 1) * (((q : k) ^ s)⁻¹) ^ 2

end Formalism.PairingDivisionLocalBalance
