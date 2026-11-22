import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCharts

universe u

namespace GroundTheory.Arith.Modular

open Polynomial Polynomial.Bivariate

namespace Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Overlap

noncomputable instance invertibleY :
    Invertible (algebraMap W.toAffine.CoordinateRing (Overlap W) (yC W)) :=
  ⟨yInv W, by rw [mul_comm]; exact yC_mul_yInv W, yC_mul_yInv W⟩

variable [Nontrivial R]

end Overlap

section Span

noncomputable def cechMap : (W.toAffine.CoordinateRing × InfChart W) →ₗ[R] Overlap W :=
  (IsScalarTower.toAlgHom R W.toAffine.CoordinateRing (Overlap W)).toLinearMap.comp
      (LinearMap.fst R _ _) -
    (infToOverlap W).toLinearMap.comp (LinearMap.snd R _ _)

@[simp]
theorem cechMap_apply (p : W.toAffine.CoordinateRing × InfChart W) :
    cechMap W p = algebraMap _ (Overlap W) p.1 - infToOverlap W p.2 := rfl

variable [Nontrivial R]

end Span

end Weierstrass

end GroundTheory.Arith.Modular
