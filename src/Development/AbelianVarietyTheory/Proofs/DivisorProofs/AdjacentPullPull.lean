import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityChangeFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSchemeTheoreticallyDominantComplEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubbundleKernelOfLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagePrincipalOfEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotMemSupportCokernelOfNeZero

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Vert

namespace GlobalTheory.FlagChain

section Sub

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

def Le (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ u : A ⟶ B, u ≫ g = f

def Same (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ e : A ≅ B, e.hom ≫ g = f

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

theorem Le.trans (h : Le f g) (h' : Le g f') : Le f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≫ v, Category.assoc ..⟩

theorem Le.map (h : Le f g) (F : C ⥤ C') : Le (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.map u, (F.map_comp ..).symm⟩

theorem Same.refl (f : A ⟶ E) : Same f f := ⟨Iso.refl _, Category.id_comp _⟩

theorem Same.symm (h : Same f g) : Same g f := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.symm, e.inv_hom_id_assoc _⟩

theorem Same.trans (h : Same f g) (h' : Same g f') : Same f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≪≫ v, Category.assoc ..⟩

theorem Same.le (h : Same f g) : Le f g := h.elim fun e he => ⟨e.hom, he⟩

theorem Same.map (h : Same f g) (F : C ⥤ C') : Same (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.mapIso u, (F.map_comp ..).symm⟩

theorem Same.comp (h : Same f g) (t : E ⟶ E') : Same (f ≫ t) (g ≫ t) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (Category.assoc ..).symm⟩

end Sub

section Covers

variable {k : Type} [CommRing k] {D : ℕ} {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsIntegral Z] {p : X ⟶ Sp k} {A E L H : X.Modules} {r : ℕ}

def IsCov (p : X ⟶ Sp k) (D : ℕ) (ρ : Y ⟶ X) : Prop :=
  IsArithVar (ρ ≫ p) D ∧ ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0

theorem IsCov.comp {ρ : Y ⟶ X} {τ : Z ⟶ Y} (h : IsCov p D ρ) (h' : IsCov (ρ ≫ p) D τ) :
    IsCov p D (τ ≫ ρ) := by
  refine ⟨(Category.assoc τ ρ p).symm ▸ h'.1, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, h'.2.1, h.2.1]
  · rw [CurveDegreesCompare.residueDegree_comp, h'.2.1]
    exact mul_ne_zero h.2.2 h'.2.2

end Covers

end GlobalTheory.FlagChain
