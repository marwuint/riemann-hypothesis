import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GenTorsMap

theorem exists_factor {K : Type} [Field K] (X : Over (Sp K)) (hX : IsFinite X.hom) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra K F] (x : Sp F ⟶ X.left) (hx : x ≫ X.hom = spMap (algebraMap K F)) :
    ∃ (σ : AlgebraicClosure K →ₐ[K] F) (x' : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X),
      x = spMap σ.toRingHom ≫ x'.left := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ X.left.isoSpec.hom)
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have hfin : c.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hc]; infer_instance
  have e : c ≫ φ = CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hc, Category.assoc, Iso.hom_inv_id_assoc, hx]
  let σ : AlgebraicClosure K →ₐ[K] F := IsAlgClosed.lift
  have hr : ∀ b, φ.hom b ∈ σ.range := fun b => by
    have hi : IsIntegral K (φ.hom b) := by
      obtain ⟨p, hp, h0⟩ := hfin.to_isIntegral b
      refine ⟨p, hp, ?_⟩
      have := congrArg φ.hom h0
      rw [Polynomial.hom_eval₂, map_zero] at this
      have e' : φ.hom.comp c.hom = algebraMap K F := congrArg CommRingCat.Hom.hom e
      rwa [e'] at this
    exact hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) σ
  have hσ : Function.Injective σ := σ.toRingHom.injective
  let φ' : Γ(X.left, ⊤) →+* AlgebraicClosure K :=
    (AlgEquiv.ofInjective σ hσ).symm.toRingEquiv.toRingHom.comp (φ.hom.codRestrict σ.range hr)
  have h1 : ∀ b, σ (φ' b) = φ.hom b := fun b =>
    congrArg Subtype.val ((AlgEquiv.ofInjective σ hσ).apply_symm_apply ⟨φ.hom b, hr b⟩)
  refine ⟨σ, Over.homMk (Spec.map (CommRingCat.ofHom φ') ≫ X.left.isoSpec.inv) ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    erw [← hc]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    apply hσ
    refine (h1 _).trans ?_
    refine Eq.trans ?_ (σ.commutes a).symm
    exact congrArg (fun g => CommRingCat.Hom.hom g a) e
  · show x = _ ≫ _ ≫ _
    rw [← Category.assoc, Iso.eq_comp_inv, ← hφ, ← Spec.map_comp]
    congr 1
    ext b
    exact (h1 b).symm

theorem hom_ext_points {K : Type} [Field K] {X Y : Over (Sp K)} (hX : IsFinite X.hom) (hE : Etale X.hom)
    (hY : IsSeparated Y.hom) (u v : X ⟶ Y)
    (h : ∀ x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X, x ≫ u = x ≫ v) : u = v := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  haveI : IsReduced X.left := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
    have he : c.hom.Etale := by
      rw [← HasRingHomProperty.Spec_iff (P := @Etale), hc]; infer_instance
    letI := c.hom.toAlgebra
    haveI : Algebra.Etale K Γ(X.left, ⊤) := he
    haveI : _root_.IsReduced Γ(X.left, ⊤) := Algebra.FormallyUnramified.isReduced_of_field K _
    exact isReduced_of_isAffine_isReduced _
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq _ _ Y.hom Set.univ dense_univ (fun z _ => ?_) (by simp)
  let F := AlgebraicClosure (X.left.residueField z)
  let i := spMap (algebraMap (X.left.residueField z) F)
  obtain ⟨c, hc⟩ := Spec.map_surjective ((i ≫ X.left.fromSpecResidueField z) ≫ X.hom)
  letI : Algebra K F := c.hom.toAlgebra
  obtain ⟨σ, x', e⟩ := exists_factor X hX F _ hc.symm
  have : Epi i := by
    have : Flat i := inferInstance
    have : Surjective i :=
      ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (X.left.residueField z)) _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi i, ← Category.assoc, ← Category.assoc]
  erw [e]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun g => _ ≫ g.left) (h x')

variable {R : Type} [CommRing R] [IsDomain R]

end GlobalTheory.GenTorsMap
