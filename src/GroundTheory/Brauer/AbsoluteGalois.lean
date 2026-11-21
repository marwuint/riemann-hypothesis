import Mathlib
import GroundTheory.Brauer.CrossedProductIso
import GroundTheory.Brauer.Inflation
import GroundTheory.Brauer.Splitting
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

namespace H2mul

section Bridge

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem ofMul_mem_cocycles₂_galUnits (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    (fun p => Additive.ofMul ((c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) p)) ∈
      cocycles₂ (galUnits.{u} K L) := by
  rw [mem_cocycles₂_iff]
  intro g h j
  exact congrArg Additive.ofMul ((mem_mulCocycles₂_iff _).1 c.2 g h j)

def galUnitsCocycle (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) : cocycles₂ (galUnits.{u} K L) :=
  ⟨_, ofMul_mem_cocycles₂_galUnits c⟩

@[simp]
theorem galUnitsCocycle_apply (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) :
    galUnitsCocycle c p = Additive.ofMul ((c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) p) :=
  rfl

def toGalUnitsH2 : mulCocycles₂ (L ≃ₐ[K] L) Lˣ →* Multiplicative (H2 (galUnits.{u} K L)) where
  toFun c := Multiplicative.ofAdd (H2π (galUnits.{u} K L) (galUnitsCocycle c))
  map_one' := by
    have h0 : galUnitsCocycle (1 : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) = 0 := Subtype.ext rfl
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    rw [h0, map_zero]
  map_mul' c c' := by
    rw [← ofAdd_add]
    congr 1
    rw [← map_add]
    rfl

theorem toGalUnitsH2_eq_one_iff (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    toGalUnitsH2 c = 1 ↔ IsMulCoboundary₂ (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) := by
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, H2π_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun g => Additive.toMul (x g), fun g h => ?_⟩
    exact congrArg Additive.toMul (congrFun hx (g, h))
  · rintro ⟨x, hx⟩
    exact ⟨fun g => Additive.ofMul (x g), funext fun p => congrArg Additive.ofMul (hx p.1 p.2)⟩

def galUnitsEquivH2 : H2mul (L ≃ₐ[K] L) Lˣ ≃* Multiplicative (H2 (galUnits.{u} K L)) :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ toGalUnitsH2 (fun c hc => (toGalUnitsH2_eq_one_iff c).2 hc)) (by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x
      induction x using induction_on with
      | h c =>
        intro hx
        exact (mk_eq_one_iff c).2 ((toGalUnitsH2_eq_one_iff c).1 hx)
    · intro y
      induction y using Multiplicative.rec with
      | ofAdd y =>
      induction y using H2_induction_on with
      | h y =>
      refine ⟨mk _ _ ⟨fun p => Additive.toMul (y p), fun g h j => ?_⟩, rfl⟩
      exact congrArg Additive.toMul ((mem_cocycles₂_iff (y : _ → Additive Lˣ)).1 y.2 g h j))

@[simp]
theorem galUnitsEquivH2_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    galUnitsEquivH2 (mk _ _ c) = Multiplicative.ofAdd (H2π (galUnits.{u} K L) (galUnitsCocycle c)) :=
  rfl

end Bridge

end H2mul

section Tower

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
  [Algebra E F] [IsScalarTower K E F] [Normal K E]

variable (K E F) in

def galUnitsInclusion :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E) (galUnits.{u} K E) ⟶
      galUnits.{u} K F :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Eˣ) (B := Additive Fˣ) (MonoidHom.toAdditive
    (Units.map ((algebraMap E F : E →+* F) : E →* F))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩

@[simp]
theorem galUnitsInclusion_hom_apply (x : Additive Eˣ) :
    ((Additive.toMul (α := Fˣ) ((galUnitsInclusion K E F).hom x) : Fˣ) : F) =
      algebraMap E F ((Additive.toMul (α := Eˣ) x : Eˣ) : E) :=
  rfl

end Tower

section Absolute

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

variable [IsGalois K Ks]

variable (K) in

def unitsInflationH2 (E : IntermediateField K Ks) [FiniteDimensional K E] [Normal K E] :
    H2 (galUnits.{u} K E) ⟶ cohomology (galUnits.{u} K Ks) 2 :=
  HomologicalComplex.homologyMap (unitsInflationCochains E) 2

end Absolute

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

section Galois

variable [IsGalois K Ks]

variable (K) in

def inflationToAbsolute (E : IntermediateField K Ks) [FiniteDimensional K E] [IsGalois K E] :
    H2mul (E ≃ₐ[K] E) Eˣ →* Multiplicative (cohomology (galUnits.{u} K Ks) 2) :=
  (AddMonoidHom.toMultiplicative (unitsInflationH2 K E).hom.toAddMonoidHom).comp
    (H2mul.galUnitsEquivH2 : H2mul (E ≃ₐ[K] E) Eˣ ≃* _).toMonoidHom

theorem inflationToAbsolute_apply (E : IntermediateField K Ks) [FiniteDimensional K E]
    [IsGalois K E] (x : H2mul (E ≃ₐ[K] E) Eˣ) :
    inflationToAbsolute K E x = Multiplicative.ofAdd
      ((unitsInflationH2 K E).hom (Multiplicative.toAdd (H2mul.galUnitsEquivH2 x))) :=
  rfl

end Galois

end Main

end GroundTheory.Brauer
