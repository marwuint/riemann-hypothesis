import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TranslateEq

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
open scoped TensorProduct

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt x ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (x.appTop.hom s) := by
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]

theorem chart_sep [Finite T] (Γ : QFGroup R T) (B : Type) [CommRing B] [Algebra R B]
    (c : Spec (CommRingCat.of B) ⟶ Γ.G.left) [IsOpenImmersion c]
    (hc : c ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (I : Type) (_ : Finite I) (τ : I → T) (e : I → B →ₐ[R] FractionRing R),
      (∀ i, Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫ c = (Γ.pt (τ i)).left) ∧
      ∀ b, (∀ i, e i b = 0) → b = 0 := by
  classical
  let I := {t : T // Set.range (Γ.pt t).left ⊆ Set.range c}
  have lift : ∀ i : I, ∃ e : B →ₐ[R] FractionRing R,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ c = (Γ.pt i.1).left := by
    intro i
    let g := IsOpenImmersion.lift c (Γ.pt i.1).left i.2
    have hg : g ≫ c = (Γ.pt i.1).left := IsOpenImmersion.lift_fac _ _ _
    let φ : B →+* FractionRing R := (Spec.preimage g).hom
    have hφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
    have hcomp : φ.comp (algebraMap R B) = algebraMap R (FractionRing R) := by
      have h1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap R B))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, ← hc, ← Category.assoc, hg]
        exact Over.w (Γ.pt i.1)
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    refine ⟨{ φ with commutes' := fun r => congr($hcomp r) }, ?_⟩
    exact (congrArg (· ≫ c) hφ).trans hg
  choose e he using lift
  refine ⟨I, inferInstance, Subtype.val, e, he, fun b hb => ?_⟩
  haveI : Flat Γ.G.hom := Γ.flat
  haveI : Module.Flat R B := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := hc ▸ inferInstance
    rw [Flat.SpecMap_iff] at this
    exact (RingHom.flat_algebraMap_iff).1 this
  haveI : IsReduced (pullback Γ.G.hom (genPt R).hom) := Γ.gen_reduced
  have hred : _root_.IsReduced (B ⊗[R] FractionRing R) := by
    have h1 : IsReduced (pullback (c ≫ Γ.G.hom) (genPt R).hom) :=
      isReduced_of_isOpenImmersion ((pullbackRightPullbackFstIso Γ.G.hom (genPt R).hom c).inv ≫ pullback.snd _ _)
    rw [hc] at h1
    have h2 : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) := h1
    have h3 := isReduced_of_isOpenImmersion (pullbackSpecIso R B (FractionRing R)).inv
    exact (affine_isReduced_iff _).1 h3
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))
  apply hinj
  rw [map_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun Q hQ => ?_)
  let P : Spec (CommRingCat.of B) := PrimeSpectrum.comap
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R).toRingHom ⟨Q, hQ⟩
  have hP : (Γ.G.hom (c P)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, hc]
    refine eq_bot_iff.2 fun r hr => ?_
    have h1 : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R) (algebraMap R B r) ∈ Q := hr
    rw [AlgHom.commutes, ← (Algebra.TensorProduct.includeRight :
      FractionRing R →ₐ[R] B ⊗[R] FractionRing R).commutes] at h1
    by_contra h0
    have h2 : algebraMap R (FractionRing R) r ≠ 0 := fun h =>
      h0 ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R (FractionRing R)) r h)
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 ((Ne.isUnit h2).map _))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hP
  have hr : Set.range (Γ.pt t).left ⊆ Set.range c := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P, by rw [← hx, Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) x y]⟩
  have hPx : Spec.map (CommRingCat.ofHom (e ⟨t, hr⟩).toRingHom) x = P :=
    c.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, he, hx])
  have hbP : b ∈ P.asIdeal := by
    rw [← hPx]
    change e ⟨t, hr⟩ b ∈ PrimeSpectrum.asIdeal x
    rw [hb]
    exact Ideal.zero_mem _
  exact hbP

theorem sec_zero [Finite T] (Γ : QFGroup R T) (s : Γ(Γ.G.left, ⊤))
    (hs : ∀ t, valAt (Γ.pt t).left ⊤ le_top s = 0) : s = 0 := by
  let 𝒰 := Γ.G.left.affineOpenCover
  refine Scheme.OpenCover.ext_elem s 0 𝒰.openCover fun k => ?_
  rw [map_zero]
  let c : Spec (CommRingCat.of (𝒰.X k)) ⟶ Γ.G.left := 𝒰.f k
  haveI : IsOpenImmersion c := 𝒰.openCover.map_prop k
  letI : Algebra R (𝒰.X k) := (Spec.preimage (c ≫ Γ.G.hom)).hom.toAlgebra
  obtain ⟨I, _, τ, e, he, hi⟩ := chart_sep Γ (𝒰.X k) c (Spec.map_preimage (c ≫ Γ.G.hom)).symm
  have h0 := hi ((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).hom (c.appTop s)) fun i => by
    have h1 := hs (τ i)
    rw [← he i, valAt_top, Scheme.Hom.comp_appTop] at h1
    exact (congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (e i).toRingHom)) (c.appTop s))).symm.trans h1
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).inv $h0)
  rw [Iso.hom_inv_id_apply, map_zero] at h2
  exact h2

def pullSec {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A)) (f : A) : Γ(X, ⊤) :=
  j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)

theorem valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (a b : Γ(X, ⊤)) : valAt x ⊤ le_top (a - b) = valAt x ⊤ le_top a - valAt x ⊤ le_top b := by
  simp only [valAt_top, map_sub]

theorem valAt_mul {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

end GlobalTheory.CompanionTheory.Ar.BT.TranslateEq
