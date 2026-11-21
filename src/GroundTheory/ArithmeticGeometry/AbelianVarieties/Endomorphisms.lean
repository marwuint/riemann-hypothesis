import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualQuadratic

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E : WeierstrassCurve F}
  [E.IsElliptic]

theorem zsmul_homId_eq_intCast (n : ℤ) : n • (homId : isogEnd E) = (n : isogEnd E) :=
  zsmul_one n

theorem intCast_isogEnd_eq_zero {n : ℤ} (h : (n : isogEnd E) = 0) : n = 0 :=
  eq_zero_of_zsmul_homId (E := E) (by rw [zsmul_homId_eq_intCast, h])

theorem intCast_isogEnd_injective : Function.Injective (Int.cast : ℤ → isogEnd E) := by
  intro m n h
  have : ((m - n : ℤ) : isogEnd E) = 0 := by rw [Int.cast_sub, h, sub_self]
  exact sub_eq_zero.mp (intCast_isogEnd_eq_zero this)

instance : CharZero (isogEnd E) where
  cast_injective m n h := by
    have : ((m : ℤ) : isogEnd E) = ((n : ℤ) : isogEnd E) := by
      rw [Int.cast_natCast, Int.cast_natCast]; exact h
    exact_mod_cast intCast_isogEnd_injective this

theorem isogEnd_one_eq_mulIsogeny :
    (1 : isogEnd E) = (mulIsogeny E 1 one_ne_zero).toHom := by
  rw [mulIsogeny_toHom, one_smul]; rfl

end GroundTheory.Arith.Abelian
