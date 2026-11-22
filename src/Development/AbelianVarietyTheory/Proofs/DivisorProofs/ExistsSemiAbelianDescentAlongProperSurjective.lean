import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsPullbackUniversallyClosedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.DescGrp

theorem quasiCompact_of_isPullback {R : Type} [CommRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) [Surjective π]
    (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom π) [QuasiCompact π]
    [QuasiCompact G'.hom] : QuasiCompact G.hom := by
  have hs : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have hc : QuasiCompact (β ≫ G.hom) := by rw [h.w]; infer_instance
  rw [quasiCompact_iff] at hc ⊢
  intro U hU hK
  have := (hc U hU hK).image β.continuous
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ hs.surj] at this

theorem exists_semiAbelian_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hp hs hi G' _ _ hG G β hsm hpb φ hφ hc
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.GrpDescent.mul_descends R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨e, he⟩ := _root_.GlobalTheory.Mum.descend_one R S π hp hs hi G' G β hpb φ hφ hc
  obtain ⟨i, hiv⟩ := _root_.GlobalTheory.Mum.exists_inv_descent R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨g, c, hP⟩ := _root_.GlobalTheory.Mum.descGrpObj_of_pullback R S π hp hs hi G' G β hsm hpb m e i hm he hiv
  haveI := hG.quasiCompact
  refine ⟨g, c, ⟨c, hsm, _root_.GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective R S π inferInstance hs G' G β hpb hG.separated,
    quasiCompact_of_isPullback π G' G β hpb,
    _root_.GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective R S π inferInstance hs G' G β hpb hG.geomConnected,
    _root_.GlobalTheory.Mum.torusExtension_of_descended R S π inferInstance hs G' G β hP hG.fibres⟩, hP⟩

end GlobalTheory.DescGrp
