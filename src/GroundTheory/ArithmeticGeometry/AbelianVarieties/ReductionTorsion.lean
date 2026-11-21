import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupTorsion

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing

section Congr

variable {F : Type*} [Field F] [DecidableEq F]

def pointCongr {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

theorem pointCongr_some {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) {x y : F}
    (hxy : W₁.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h
  rfl

end Congr

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

variable [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

def reduceTorsionHom (n : ℕ) :
    AddSubgroup.torsionBy (E0 K W) n →+ AddSubgroup.torsionBy (curveRed W).Point n :=
  ((reduceHom K W).comp (AddSubgroup.torsionBy (E0 K W) n).subtype).codRestrict _ fun P => by
    rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.comp_apply, ← map_nsmul,
      AddSubgroup.subtype_apply, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero]

theorem coe_reduceTorsionHom_apply (n : ℕ) (P : AddSubgroup.torsionBy (E0 K W) n) :
    (reduceTorsionHom K W n P : (curveRed W).Point) = reduceHom K W P :=
  rfl

end

end GroundTheory.Arith.Abelian
