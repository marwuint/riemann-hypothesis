import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalHomFactorsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroDeformationFactorsThroughLinear

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem exists_dir_eq_of_smooth : ∀ (k₀ : Type) [Field k₀] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k₀)) (n : ℕ),
    SmoothOfRelativeDimension n s → ∀ (K : Type) [Field K] (κ : k₀ →+* K) (ι : Type) [Fintype ι],
    Fintype.card ι = n → ∀ Xι : Spec (CommRingCat.of (TrivSqZeroExt K (ι → K))) ⟶ X,
    Xι ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K (ι → K)).comp κ)) →
    (∀ M M' : ι → K,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom) ≫ Xι → M = M') →
    ∀ x' : Spec (CommRingCat.of (DualNumber K)) ⟶ X,
    x' ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K K).comp κ)) →
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ x' =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι →
    ∃ M : ι → K, x' = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι := by
  intro k₀ _ X s n hs K _ κ ι _ hι Xι hXs hinj x' hx's hred
  have hloc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      IsLocalHom (TrivSqZeroExt.fstHom K K M).toRingHom :=
    fun M _ _ _ _ => ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  have cp : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom) (IsLocalRing.closedPoint K) =
        IsLocalRing.closedPoint (TrivSqZeroExt K M) := fun M _ _ _ _ => by
    haveI := hloc M
    exact IsLocalRing.comap_closedPoint _
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := hs.exists_isStandardSmoothOfRelativeDimension
    ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι) (IsLocalRing.closedPoint K))
  have h1 : Xι (IsLocalRing.closedPoint (TrivSqZeroExt K (ι → K))) ∈ V := by
    rw [← cp]; exact hxV
  have h2 : x' (IsLocalRing.closedPoint (DualNumber K)) ∈ V := by
    rw [← cp]; have := hxV; rw [← hred] at this; exact this
  obtain ⟨R, rfl⟩ := _root_.GlobalTheory.spec_local_hom_factors_affineOpen X V hV _ Xι h1
  obtain ⟨g, rfl⟩ := _root_.GlobalTheory.spec_local_hom_factors_affineOpen X V hV _ x' h2
  letI := (s.appLE U V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) := hstd
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have mono : ∀ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {A : Type} [CommRing A] (φ ψ : Γ(Y, W) →+* A),
      Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec → φ = ψ := by
    intro Y W hW A _ φ ψ h
    have := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
    exact congrArg CommRingCat.Hom.hom this
  have hsp : ∀ {A : Type} [CommRing A] (φ : Γ(X, V) →+* A),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom (φ.comp (s.appLE U V e).hom)) ≫ hU.fromSpec := by
    intro A _ φ
    rw [Category.assoc, ← key, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
      (φ : Γ(X, V) →+* TrivSqZeroExt K M),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) →
      ∀ a, φ (s.appLE U V e a) = TrivSqZeroExt.inl (φ (s.appLE U V e a)).fst := by
    intro M _ _ _ _ φ hφ a
    have e1 := hsp φ
    have e2 : Spec.map (CommRingCat.ofHom (((TrivSqZeroExt.inlHom K M).comp (TrivSqZeroExt.fstHom K K M).toRingHom).comp
        (φ.comp (s.appLE U V e).hom))) ≫ hU.fromSpec =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← e1, hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have := mono hU _ _ (e2.trans (hφ.symm.trans e1))
    exact (RingHom.congr_fun this a).symm
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.FirstOrderPoints.exists_linearCombination_eq Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) K n hstd ι hι R (hc _ R hXs)
    (fun M M' h => hinj M M' (by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, h]))
    g (fun b => by
      have := mono hV ((TrivSqZeroExt.fstHom K K K).toRingHom.comp g) ((TrivSqZeroExt.fstHom K K (ι → K)).toRingHom.comp R) (by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
        exact hred)
      exact RingHom.congr_fun this b)
    (hc _ g hx's)
  refine ⟨M, ?_⟩
  rw [hM, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end GlobalTheory.FlagTan
