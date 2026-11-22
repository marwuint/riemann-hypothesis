import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.GlobalReciprocity.Frobenius
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import GroundTheory.GlobalFields.ClassFieldConsequences.ConductorLocal
import GroundTheory.GlobalFields.Artin.InflationTower

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField WithZero

noncomputable section

section Circle

variable {G : Type*} [Group G] [Finite G]

theorem norm_coe_apply_eq_one (χ : G →* ℂˣ) (g : G) : ‖((χ g : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((χ g : ℂˣ) : ℂ) ^ Nat.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

def toCircleHom (χ : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(χ g : ℂ), mem_sphere_zero_iff_norm.2 (norm_coe_apply_eq_one χ g)⟩
  map_one' := Circle.ext (by simp)
  map_mul' x y := Circle.ext (by
    change ((χ (x * y) : ℂˣ) : ℂ) = (χ x : ℂ) * (χ y : ℂ)
    rw [map_mul, Units.val_mul])

@[simp]
theorem coe_toCircleHom (χ : G →* ℂˣ) (g : G) : (toCircleHom χ g : ℂ) = χ g :=
  rfl

end Circle

section CharField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

abbrev charField : IntermediateField K L :=
  fixedField χ.ker

def charBar : (charField χ ≃ₐ[K] charField χ) →* ℂˣ :=
  (QuotientGroup.kerLift χ).comp (IsGalois.normalAutEquivQuotient χ.ker).symm.toMonoidHom

@[simp]
theorem charBar_restrictNormalHom (σ : Gal(L/K)) :
    charBar χ (AlgEquiv.restrictNormalHom (charField χ) σ) = χ σ := by
  rw [charBar, MonoidHom.comp_apply, ← IsGalois.normalAutEquivQuotient_apply]
  simp

theorem charBar_injective : Function.Injective (charBar χ) :=
  (QuotientGroup.kerLift_injective χ).comp (MulEquiv.injective _)

instance isMulCommutative_charField : IsMulCommutative (charField χ ≃ₐ[K] charField χ) :=
  ⟨⟨fun a b ↦ charBar_injective χ (by rw [map_mul, map_mul, mul_comm])⟩⟩

end CharField

section Hecke

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

def heckeCharacterOfChar : HeckeCharacter K where
  toMonoidHom := (toCircleHom (charBar χ)).comp (reciprocityMap K (charField χ))
  continuous_toFun :=
    (continuous_of_discreteTopology (f := toCircleHom (charBar χ))).comp continuous_reciprocityMap

end Hecke

section Places

theorem IsArithFrobAt.eq_of_inertia_eq_bot {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] {Q : Ideal S}
    (hI : Q.inertia G = ⊥) {σ σ' : G} (h : IsArithFrobAt R σ Q) (h' : IsArithFrobAt R σ' Q) :
    σ = σ' := by
  have := h.mul_inv_mem_inertia h'
  rwa [hI, Subgroup.mem_bot, mul_inv_eq_one] at this

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

instance liesOver_under_charField :
    w.asIdeal.LiesOver (w.under (𝓞 (charField χ))).asIdeal :=
  ⟨rfl⟩

instance liesOver_under_charField_base :
    (w.under (𝓞 (charField χ))).asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.tower_bot w.asIdeal _ v.asIdeal

end Places

end

end GroundTheory.Global
