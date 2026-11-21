import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcObjIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIsEm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelAmpleOfAffineOpenMeetsFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFiniteTypeIntFiniteIndexProdNormalDomains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepOfFiniteProductAlgebras
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualConStep

def conductor (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] : Ideal R where
  carrier := {x | ∀ r : R', ∃ y : R, algebraMap R R' y = algebraMap R R' x * r}
  add_mem' {x x'} hx hx' r := by
    obtain ⟨y, hy⟩ := hx r
    obtain ⟨y', hy'⟩ := hx' r
    exact ⟨y + y', by rw [map_add, map_add, hy, hy', add_mul]⟩
  zero_mem' r := ⟨0, by simp⟩
  smul_mem' b {x} hx r := by
    obtain ⟨y, hy⟩ := hx r
    exact ⟨b * y, by rw [smul_eq_mul, map_mul, map_mul, hy, _root_.mul_assoc]⟩

theorem conductor_mul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] :
    ∀ x ∈ conductor R R', ∀ r : R', ∃ y ∈ conductor R R', algebraMap R R' y = algebraMap R R' x * r := by
  intro x hx r
  obtain ⟨y, hy⟩ := hx r
  refine ⟨y, fun r' ↦ ?_, hy⟩
  obtain ⟨z, hz⟩ := hx (r * r')
  exact ⟨z, by rw [hz, hy, _root_.mul_assoc]⟩

theorem hasRepAF_factor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (V : A.left.Opens) (hV : IsAffineOpen V)
    (hVs : ∀ s : Sp R, ∃ x ∈ V, A.hom x = s) (D : Type) [CommRing D] [Algebra R D] [IsNoetherianRing D]
    [IsDomain D] [IsIntegrallyClosed D] :
    HasRepAF A g (Over.mk (spMap (algebraMap R D))) := by
  set f := algebraMap R D
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) _ g hP hA hg
  haveI : IsAffineHom (pullback.fst A.hom (spMap f)) :=
    (AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{0}).of_isPullback (IsPullback.of_hasPullback _ _).flip
      (inferInstance : IsAffineHom (spMap f))
  have hV' : IsAffineOpen (pullback.fst A.hom (spMap f) ⁻¹ᵁ V) := hV.preimage _
  have hVs' : ∀ s : Sp D, ∃ x ∈ pullback.fst A.hom (spMap f) ⁻¹ᵁ V,
      ((Over.pullback (spMap f)).obj A).hom x = s := by
    intro s
    obtain ⟨x, hx, hxs⟩ := hVs (spMap f s)
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x s hxs
    exact ⟨z, by simpa [hz1] using hx, hz2⟩
  obtain ⟨L, hL, hLa⟩ := _root_.GlobalTheory.ProjNormal.exists_relAmple_of_affine D _ hA' _ hV' hVs'
  have h1 := _root_.GlobalTheory.DualPol.hasRepAF_of_relAmple D _ g hA' hg' L hL hLa
  have h2 := ((_root_.GlobalTheory.DualCon.hasRep_baseChange_iff _ _ (spMap f) A _ _ hP g (𝟙_ _)).2).1 h1
  simpa using h2

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ _ A _ g hA hg V hV hVs hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : IsEmpty (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    obtain ⟨B, b, P, hP, hG, -⟩ := _root_.GlobalTheory.DualCon.hasRepAF_of_isEmpty _ A (𝟙_ _) g this
    exact ⟨B, b, P, hP, hG⟩
  obtain ⟨n, D, iR, iA, hD, hinj, a, ha0, ha⟩ := _root_.GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains R
  have hfac : ∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i)))) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hD i
    haveI : IsNoetherianRing (D i) := by
      haveI : Algebra.FiniteType R (D i) := inferInstance
      exact Algebra.FiniteType.isNoetherianRing R (D i)
    exact hasRepAF_factor R A g hA hg V hV hVs (D i)
  haveI : ∀ i, Module.Finite R (D i) := fun i ↦ (hD i).2.2
  have hprod := _root_.GlobalTheory.DualCon.ProdGlue.hasRepAF_pi R A g hA n D hfac
  have hac : a ∈ conductor R (∀ i, D i) := ha
  have hc : conductor R (∀ i, D i) ≠ ⊥ := fun h ↦ ha0 (by rw [h] at hac; exact (Submodule.mem_bot R).1 hac)
  exact _root_.GlobalTheory.Pinch.hasRep_pinched R A g hA hg (∀ i, D i) hinj _ conductor_mul hprod (hJ _ hc)

end GlobalTheory.DualConStep
