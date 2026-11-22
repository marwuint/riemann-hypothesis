import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveClosure

open TensorProduct

theorem isReduced_pullback_localization : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (V : Scheme.{0}) [IsReduced V] (f : V ⟶ Sp R), IsReduced (pullback f (spMap (algebraMap R S))) := by
  intro R S _ _ _ M _ V _ f
  let 𝒰 := Scheme.Pullback.openCoverOfLeft V.affineOpenCover.openCover f (spMap (algebraMap R S))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := V.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (V.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (V.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (V.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra R (V.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 : IsReduced (V.affineOpenCover.X i ⊗[R] S) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (V.affineOpenCover.X i) M) _ h1
    have h3 := (affine_isReduced_iff (.of (V.affineOpenCover.X i ⊗[R] S))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R (V.affineOpenCover.X i) S).hom
  exact IsReduced.of_openCover _ 𝒰

theorem exists_iso_red_of_range : ∀ (X G : Scheme.{0}) (g : G ⟶ X) [IsClosedImmersion g] [IsReduced G] (Z : Closeds X), Set.range g = (Z : Set X) → ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G, e.hom ≫ g = redι Z := by
  intro X G g _ _ Z h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z = g.ker := by
    rw [← InterModel.radical_ker g, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq, h]
  show ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G,
    e.hom ≫ g = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [hker]
  refine ⟨(asIso g.toImage).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact g.toImage_imageι.symm

end GlobalTheory.CurveClosure
