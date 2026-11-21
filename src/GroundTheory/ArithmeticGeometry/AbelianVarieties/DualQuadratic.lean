import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualWeil

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E E' : WeierstrassCurve F}
  [E.IsElliptic] [E'.IsElliptic]

theorem mulIsogeny_toHom (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).toHom = n • (homId : isogEnd E) :=
  Subtype.ext (by rw [Isogeny.toHom_val, Isogeny.mulIsogeny_val]; rfl)

theorem eq_zero_of_zsmul_homId {n : ℤ} (h : n • (homId : isogEnd E) = 0) : n = 0 := by
  by_contra hn
  rw [← mulIsogeny_toHom n hn] at h
  exact (mulIsogeny E n hn).toHom_ne_zero h

namespace Isogeny

end Isogeny

end GroundTheory.Arith.Abelian
