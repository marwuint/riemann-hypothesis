import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor

open CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

section TwoOpens

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

abbrev i01 : Fin 2 → Fin 2 := ![0, 1]

end TwoOpens

end GroundTheory.Arith.Modular
