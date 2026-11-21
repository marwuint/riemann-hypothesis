import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjOfFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoPoint

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J

end UpperTheory.V.J

theorem UpperTheory.V.J.coPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (y : R →ₐ[c.O] Qbar l),
        Module.Finite c.O y.range ∧ (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal R, ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.CoPoint.coPt
