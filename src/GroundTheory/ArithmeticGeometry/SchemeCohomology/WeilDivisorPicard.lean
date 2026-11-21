import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorInvertible
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Picard

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

noncomputable def weilDivisorToPic : WeilDivisor X →+ Additive (Pic X) where
  toFun D := Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D))
  map_zero' := by
    rw [ofMul_eq_zero, ← Pic.mk_unit, Pic.mk_eq_mk_iff]
    exact ⟨divisorSheafZeroIso.symm⟩
  map_add' D E := by
    rw [← ofMul_mul, ← Pic.mk_tensor]
    congr 1
    exact (Pic.mk_eq_mk_iff _ _).mpr ⟨(divisorTensorIso D E).symm⟩

lemma weilDivisorToPic_apply (D : WeilDivisor X) :
    weilDivisorToPic D =
      Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D)) := rfl

end GroundTheory.Arith.SchemeCoh
