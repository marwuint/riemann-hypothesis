import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaExtend

theorem isRegularRing_sections {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsRegularRing Γ(Y, V) := by
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  rw [isRegularRing_iff]
  intro q hq
  let y : PrimeSpectrum Γ(Y, V) := ⟨q, hq⟩
  have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (hV.fromSpec y)) :=
    Y.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hy⟩
  have h : IsLocalization q.primeCompl (Y.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hy
  have := hY (hV.fromSpec y)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Y.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_stalk {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (f : X ⟶ Y) [Smooth f] (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  have hs : (f.appLE V U hUV).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have := isRegularRing_sections hY hV
  algebraize [(f.appLE V U hUV).hom]
  have : IsRegularRing Γ(X, U) := isRegularRing_of_smooth Γ(Y, V) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact ExtendRig.isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem ufd_of_regular (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE R

end GlobalTheory.ThetaExtend
