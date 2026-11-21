import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

private theorem specOf_prime {B : Type} [CommRing B] {T : Scheme.{0}} (ξ : B →+* Γ(T, ⊤)) (t : T) :
    (show PrimeSpectrum B from specOf ξ t).asIdeal =
      ((show PrimeSpectrum Γ(T, ⊤) from T.toSpecΓ t).asIdeal).comap ξ := by
  rfl

end UpperTheory
