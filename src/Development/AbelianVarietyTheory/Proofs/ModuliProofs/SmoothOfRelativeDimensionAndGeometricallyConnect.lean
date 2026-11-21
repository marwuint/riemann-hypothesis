import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedGenericFibreOfDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VeryDenseFibres

theorem smooth_fiber_of_smooth_fiber {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : Smooth ((pullback.snd f t).fiberToSpecResidueField y)) :
    Smooth (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  · infer_instance
  · infer_instance

theorem mem_smoothLocus_of_smooth_fiber {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    (h : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have _ : Smooth (pullback.snd f ((Spec R).fromSpecResidueField
        ((X.affineCover.f i ≫ f) y))) := h
    have H := this (X.affineCover.f i ≫ f) y (by
      rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  haveI : Module.Flat R S :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp ‹_›
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let p : PrimeSpectrum R := Spec.map φ x
  haveI : x.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  haveI : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ↑S)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth) (Spec.fiberToSpecResidueFieldIso R S p)]
    exact h
  haveI := Algebra.IsSmoothAt.of_formallySmooth_fiber (R := R) p.asIdeal x.asIdeal
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem exists_opens_smoothOfRelativeDimension {X T S : Scheme.{0}} (f : X ⟶ S) [Smooth f]
    (t : T ⟶ S) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd f t)) (x : X) (y : T)
    (hxy : f x = t y) : ∃ W : X.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ f) := by
  obtain ⟨n, W, hW, hd⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim f x
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  have h1 : SmoothOfRelativeDimension n (pullback.snd (W.ι ≫ f) t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ hd
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (W.ι ≫ f) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (W.ι ≫ f) t)
    ⟨x, hW⟩ y hxy
  have e : n = g := by simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  exact ⟨W, hW, e ▸ hd⟩

theorem eq_top_of_forall_mem {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    [UniversallyClosed s] (P : Set (Ideal R))
    (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p) (U : Z.Opens)
    (hU : ∀ z : Z, (s z).asIdeal ∈ P → z ∈ U) : U = ⊤ := by
  rw [← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (PrimeSpectrum.isPrime _)
  have hs : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hs.mem_closed hc ⟨x, hx, rfl⟩
  exact hy (hU y (by rw [hy']; exact hp))

theorem spMap_apply_asIdeal {R K : Type} [CommRing R] [Field K] (x : R →+* K) (y : Sp K) :
    (spMap x y).asIdeal = RingHom.ker x := by
  have : y.asIdeal = ⊥ := by
    have := PrimeSpectrum.isPrime y
    exact Ideal.eq_bot_of_prime _
  change Ideal.comap x y.asIdeal = _
  rw [this]
  rfl

end GlobalTheory.VeryDenseFibres
