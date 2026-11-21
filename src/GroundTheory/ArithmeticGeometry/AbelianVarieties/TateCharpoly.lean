import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualQuadratic
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilPairing
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilGaloisFunctionField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TateModule

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve PadicInt

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]

namespace TateCharpoly

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem homPt_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homPt (homComp R Q) = (homPt R).comp (homPt Q) := by
  by_cases hQ : Q = 0
  · subst hQ
    rw [homComp_zero_right, homPt_zero, homPt_zero, AddMonoidHom.comp_zero]
  by_cases hR : R = 0
  · subst hR
    rw [homComp_zero_left, homPt_zero, homPt_zero, AddMonoidHom.zero_comp]
  obtain ⟨φ, rfl⟩ : ∃ φ : Isogeny E E', φ.toHom = Q := ⟨isogOfHom Q hQ, rfl⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Isogeny E' E'', ψ.toHom = R := ⟨isogOfHom R hR, rfl⟩
  rw [Isogeny.homComp_toHom, homPt_toHom, homPt_toHom, homPt_toHom]
  ext P
  rw [AddMonoidHom.comp_apply, Isogeny.pointHom_apply, Isogeny.pointHom_apply,
    Isogeny.pointHom_apply, Isogeny.pointMap_comp]

theorem homId_eq_mulIsogeny : (homId : isogEnd E) = (mulIsogeny E 1 one_ne_zero).toHom := by
  rw [mulIsogeny_toHom, one_smul]

theorem homPt_homId : homPt (homId : isogEnd E) = AddMonoidHom.id _ := by
  rw [homId_eq_mulIsogeny, homPt_toHom]
  ext P
  rw [Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, one_smul, AddMonoidHom.id_apply]

end TateCharpoly

open TateCharpoly

variable {E : WeierstrassCurve F} [E.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

noncomputable def endTate : isogEnd E →+* Module.End ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) where
  toFun a := TateModule.map (homPt a)
  map_one' := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [TateModule.map_apply]
    show homPt (homId : isogEnd E) _ = _
    rw [homPt_homId]
    rfl
  map_mul' a b := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [Module.End.mul_apply, TateModule.map_apply, TateModule.map_apply, TateModule.map_apply,
      isogEnd_mul_def, homPt_homComp, AddMonoidHom.comp_apply]
  map_zero' := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [TateModule.map_apply, homPt_zero, AddMonoidHom.zero_apply]
    rfl
  map_add' a b := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [LinearMap.add_apply, TateModule.map_apply, AddSubgroup.coe_add, Pi.add_apply,
      TateModule.map_apply, TateModule.map_apply, homPt_add, AddMonoidHom.add_apply]

theorem endTate_apply (a : isogEnd E) (t : TateModule ℓ E.toAffine.Point) (k : ℕ) :
    ((endTate ℓ a t : TateModule ℓ E.toAffine.Point) : ℕ → E.toAffine.Point) k =
      homPt a ((t : ℕ → E.toAffine.Point) k) :=
  rfl

variable {ℓ}

namespace TateCharpoly

end TateCharpoly

instance TateCharpoly.instFreeTateModule [hℓF : Fact ((ℓ : F) ≠ 0)] :
    Module.Free ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) :=
  tateModule_free E ℓ hℓF.out

instance TateCharpoly.instFiniteTateModule [hℓF : Fact ((ℓ : F) ≠ 0)] :
    Module.Finite ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) :=
  Module.Finite.of_basis (tateModule_basis E ℓ hℓF.out).some

end GroundTheory.Arith.Abelian
