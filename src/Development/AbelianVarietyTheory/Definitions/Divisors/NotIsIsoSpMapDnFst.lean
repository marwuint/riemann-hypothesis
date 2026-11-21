import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

variable {S : Scheme.{0}}

def ptMap {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    Over.mk (spMap φ ≫ s) ⟶ Over.mk s := Over.homMk (spMap φ)

@[simp] theorem ptMap_left {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    (ptMap s φ).left = spMap φ := rfl

abbrev dnInl (k : Type) [CommRing k] : k →+* DualNumber k := algebraMap k (DualNumber k)

abbrev dnFst (k : Type) [CommRing k] : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

structure Milnor {T T₁ T₂ T₀ : Scheme.{0}} (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) : Prop where
  aff : IsAffine T
  aff₁ : IsAffine T₁
  aff₂ : IsAffine T₂
  closed : IsClosedImmersion k₂
  w : k₁ ≫ j₁ = k₂ ≫ j₂
  cart : IsPullback j₁.appTop j₂.appTop k₁.appTop k₂.appTop

variable (A : Over S) [GrpObj A] {U : Over S} (M : LB (A ⊗ U).left)

def FieldChart : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (T : Over S) (_ : T ⟶ Over.mk s) (N : LB (A ⊗ T).left),
    Fam A N → ChartAt A M N

def TanLift : Prop :=
  ∀ (k : Type) [Field k] (s : Sp k ⟶ S) (N : LB (A ⊗ Over.mk (spMap (dnInl k) ≫ s)).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) ⟶ U, Same A N M (ptMap _ (dnFst k)) u₀ →
      ∃ u : Over.mk (spMap (dnInl k) ≫ s) ⟶ U, Same A N M (𝟙 _) u

def SmallLift : Prop :=
  ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C →
    (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ s) ⟶ U,
      Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) u₀ → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u

variable {A M}

theorem Milnor.id (T : Scheme.{0}) [IsAffine T] : Milnor (𝟙 T) (𝟙 T) (𝟙 T) (𝟙 T) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, rfl, by
    simpa using IsPullback.of_id_fst (f := 𝟙 Γ(T, ⊤))⟩

theorem Milnor.of_isPullback {R R₁ R₂ R₀ : CommRingCat.{0}} {a : R ⟶ R₁} {b : R ⟶ R₂} {c : R₁ ⟶ R₀} {d : R₂ ⟶ R₀}
    (h : IsPullback a b c d) (hd : Function.Surjective d) :
    Milnor (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d) where
  aff := inferInstance
  aff₁ := inferInstance
  aff₂ := inferInstance
  closed := IsClosedImmersion.spec_of_surjective d hd
  w := by rw [← Spec.map_comp, ← Spec.map_comp, h.w]
  cart := h.of_iso (Scheme.ΓSpecIso R).symm (Scheme.ΓSpecIso R₁).symm (Scheme.ΓSpecIso R₂).symm
    (Scheme.ΓSpecIso R₀).symm (by simp) (by simp) (by simp) (by simp)

end GlobalTheory.DualOpen
