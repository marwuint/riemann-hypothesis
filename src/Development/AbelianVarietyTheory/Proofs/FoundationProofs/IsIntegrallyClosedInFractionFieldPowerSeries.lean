import Mathlib

open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.OnePoint

universe u v w

section Algebra

variable {K : Type u} [Field K]

theorem exists_algHom_of_isIntegrallyClosedIn {L : Type w} [Field L] [Algebra K L]
    [IsIntegrallyClosedIn K L] {A : Type v} [CommRing A] [Algebra K A] [Algebra.IsIntegral K A]
    (φ : A →ₐ[K] L) : ∃ ψ : A →ₐ[K] K, (Algebra.ofId K L).comp ψ = φ := by
  have hmem : ∀ a : A, φ a ∈ (Algebra.ofId K L).range := fun a ↦
    (isIntegrallyClosedIn_iff.mp ‹_›).2 ((Algebra.IsIntegral.isIntegral (R := K) a).map φ)
  let e := AlgEquiv.ofInjective (Algebra.ofId K L) (algebraMap K L).injective
  refine ⟨(e.symm : _ →ₐ[K] K).comp (φ.codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict _ hmem a))

end Algebra

section Scheme

local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))

variable {K : Type u} [Field K]

theorem epi_of_nonempty {T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K)) : Epi g :=
  have : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective g

theorem point_ext {X T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K))
    {s s' : Spec (.of K) ⟶ X} (h : g ≫ s = g ≫ s') : s = s' :=
  have := epi_of_nonempty g
  (cancel_epi g).mp h

theorem exists_section_of_locallyQuasiFinite {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ F) (hx : x ≫ f = specAlg(K, L)) :
    ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₁ = x → x₁ = x₀ := by
  suffices H : ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, L) ≫ x₀ = x by
    obtain ⟨x₀, h₀⟩ := H
    refine ⟨x₀, h₀, point_ext specAlg(K, L) ?_, fun x₁ h₁ ↦ point_ext _ (h₁.trans h₀.symm)⟩
    rw [reassoc_of% h₀, hx, Category.comp_id]
  obtain ⟨A, i, _, q, hq⟩ := Scheme.exists_Spec_apply_eq (x (Classical.arbitrary _))
  have hle : Set.range x ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨q, hq.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ i = x := ⟨_, IsOpenImmersion.lift_fac i x hle⟩
  obtain ⟨a, rfl⟩ := Spec.map_surjective l
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hqf : φ.hom.QuasiFinite := by
    have : LocallyQuasiFinite (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.QuasiFinite K A := hqf
  have : Module.Finite K A := .of_quasiFinite
  rw [Category.assoc, ← hφ, ← Spec.map_comp] at hx
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
  let a' : A →ₐ[K] L := ⟨a.hom, fun c ↦ DFunLike.congr_fun hc c⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_isIntegrallyClosedIn a'
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext t
  exact DFunLike.congr_fun hψ t

theorem exists_point_of_locallyQuasiFinite {X Y : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyQuasiFinite κ] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ X) (y : Spec (.of K) ⟶ Y) (hx : x ≫ κ = specAlg(K, L) ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₁ = x → x₁ = x₀ := by
  obtain ⟨s, hs, hs', -⟩ := exists_section_of_locallyQuasiFinite (K := K) (pullback.snd κ y) L
    (pullback.lift x _ hx) (pullback.lift_snd _ _ _)
  have hg : specAlg(K, L) ≫ s ≫ pullback.fst κ y = x := by
    rw [reassoc_of% hs, pullback.lift_fst]
  refine ⟨s ≫ pullback.fst κ y, hg, ?_, fun x₁ h₁ ↦ point_ext _ (h₁.trans hg.symm)⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hs']

end Scheme
end GlobalTheory.OnePoint
