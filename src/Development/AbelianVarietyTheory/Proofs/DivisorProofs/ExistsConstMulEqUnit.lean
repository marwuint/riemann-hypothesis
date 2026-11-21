import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

section Units

variable {X : Scheme.{0}} [IsIntegral X]

def UnitAt (x : X) (t : X.functionField) : Prop :=
  ∃ u : (X.presheaf.stalk x)ˣ, algebraMap _ X.functionField (u : X.presheaf.stalk x) = t

theorem UnitAt.mul {x : X} {s t : X.functionField} (hs : UnitAt x s) (ht : UnitAt x t) : UnitAt x (s * t) := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨v, rfl⟩ := ht
  exact ⟨u * v, by rw [Units.val_mul, map_mul]⟩

theorem UnitAt.inv {x : X} {s : X.functionField} (hs : UnitAt x s) : UnitAt x s⁻¹ := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨u⁻¹, by rw [map_units_inv]⟩

theorem UnitAt.ne_zero {x : X} {s : X.functionField} (hs : UnitAt x s) : s ≠ 0 := by
  obtain ⟨u, rfl⟩ := hs
  exact (u.isUnit.map _).ne_zero

theorem isOpen_unitAt (t : X.functionField) : IsOpen {x : X | UnitAt x t} := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro x ⟨u, hu⟩
  obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk x)
  refine ⟨X.basicOpen s, fun y hy => ?_, (X.basicOpen s).isOpen,
    (X.mem_basicOpen s x hV).2 (by rw [hs]; exact u.isUnit)⟩
  have hyV := X.basicOpen_le s hy
  refine ⟨((X.mem_basicOpen s y hyV).1 hy).unit, ?_⟩
  rw [← hu, ← hs, IsUnit.unit_spec]
  exact (X.presheaf.germ_stalkSpecializes_apply hyV _ _).trans
    (X.presheaf.germ_stalkSpecializes_apply hV _ _).symm

theorem exists_unit_eq [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (V : X.Opens) [Nonempty V]
    (t : X.functionField) (h0 : t ≠ 0) (h : ∀ x ∈ V, Order.coheight x = 1 → UnitAt x t) :
    ∃ u : Γ(X, V)ˣ, X.germToFunctionField V u = t := by
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t fun x hx h1 =>
    let ⟨u, hu⟩ := h x hx h1; ⟨u, hu⟩
  obtain ⟨s', hs'⟩ := exists_germToFunctionField_eq_of_coheight_eq_one V t⁻¹ fun x hx h1 =>
    let ⟨u, hu⟩ := (h x hx h1).inv; ⟨u, hu⟩
  have : IsUnit s := IsUnit.of_mul_eq_one s' (X.germToFunctionField_injective V (by
    rw [map_mul, hs, hs', map_one, mul_inv_cancel₀ h0]))
  exact ⟨this.unit, hs⟩

end Units

theorem constFn_top {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp A) (a : A) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a = q.appTop ((Scheme.ΓSpecIso (.of A)).inv a) :=
  congrArg (fun m : Γ(Sp A, ⊤) ⟶ Γ(X, ⊤) => m ((Scheme.ΓSpecIso (.of A)).inv a)) (q.appLE_eq_app (U := ⊤))

theorem app_constFn {A C : Type} [CommRing A] [CommRing C] {g : A →+* C} {X Y : Scheme.{0}} {q : X ⟶ Sp A}
    {p : Y ⟶ Sp C} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (a : A) :
    φ.app ⊤ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn q ⊤ a) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p ⊤ (g a) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp A ↦ φ.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) w
  have h₂ := congrArg (fun φ : CommRingCat.of A ⟶ Γ(Spec (.of C), ⊤) ↦ φ a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [constFn_top, constFn_top]
  exact h₁.trans (congrArg p.appTop h₂.symm)

section Transport

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X) (hφ : φ (genericPoint Y) ⤳ genericPoint X)

noncomputable def ffMap : X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes hφ ≫ φ.stalkMap (genericPoint Y)

theorem ffMap_germ (V : X.Opens) [Nonempty V] (W : Y.Opens) [Nonempty W] (h : W ≤ φ ⁻¹ᵁ V) (s : Γ(X, V)) :
    ffMap φ hφ (X.germToFunctionField V s) = Y.germToFunctionField W (φ.appLE V W h s) := by
  refine (congrArg (φ.stalkMap _) (X.presheaf.germ_stalkSpecializes_apply _ hφ s)).trans
    ((φ.germ_stalkMap_apply V _ _ s).trans ?_)
  exact (Y.presheaf.germ_res_apply (homOfLE h) _ _ _).symm

variable [∀ y, IsIso (φ.stalkMap y)]

theorem ffMap_bijective : Function.Bijective (ffMap φ hφ) := by
  have : IsIso (X.presheaf.stalkSpecializes hφ) :=
    (X.presheaf.stalkCongr ((genericPoint_specializes _).antisymm hφ)).isIso_hom
  have : IsIso (ffMap φ hφ) := by unfold ffMap; infer_instance
  exact ConcreteCategory.bijective_of_isIso _

theorem unitAt_of_isUnit {W : Y.Opens} [Nonempty W] {τ : Γ(Y, W)} (hτ : IsUnit τ) {y : Y} (hy : y ∈ W)
    {t : X.functionField} (ht : ffMap φ hφ t = Y.germToFunctionField W τ) : UnitAt (φ y) t := by
  obtain ⟨σ, hσ⟩ := (ConcreteCategory.bijective_of_isIso (φ.stalkMap y)).2 (Y.presheaf.germ W y hy τ)
  have hu : IsUnit σ := (isUnit_map_iff (φ.stalkMap y).hom σ).1 (by
    rw [hσ]; exact hτ.map _)
  refine ⟨hu.unit, (ffMap_bijective φ hφ).1 ?_⟩
  rw [ht, IsUnit.unit_spec]
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq σ
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : Nonempty (φ ⁻¹ᵁ V) := ⟨⟨y, hV⟩⟩
  refine (congrArg (ffMap φ hφ) (X.presheaf.germ_stalkSpecializes_apply hV _ s)).trans
    ((ffMap_germ φ hφ V (φ ⁻¹ᵁ V) le_rfl s).trans ?_)
  rw [φ.germ_stalkMap_apply] at hσ
  rw [φ.appLE_eq_app]
  have := congrArg (Y.presheaf.stalkSpecializes (genericPoint_specializes y)) hσ
  rwa [Y.presheaf.germ_stalkSpecializes_apply, Y.presheaf.germ_stalkSpecializes_apply] at this

end Transport

open MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

end GlobalTheory.VerticalUnit
