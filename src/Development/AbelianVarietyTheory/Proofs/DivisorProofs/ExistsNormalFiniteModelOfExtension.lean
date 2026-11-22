import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BplusDescent

section Field

variable {X : Scheme.{0}} [IsIntegral X] {L : Type} [Field L] (φ : X.presheaf.stalk (genericPoint X) ⟶ .of L)

abbrev fieldPt : Spec (.of L) ⟶ X := Spec.map φ ≫ X.fromSpecStalk (genericPoint X)

theorem fieldPt_apply (x : Spec (.of L)) : fieldPt φ x = genericPoint X := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have : Spec.map φ x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
  change X.fromSpecStalk _ (Spec.map φ x) = _
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

theorem top_le_fieldPt {U : X.Opens} (hU : genericPoint X ∈ U) : ⊤ ≤ fieldPt φ ⁻¹ᵁ U := fun x _ => by
  change fieldPt φ x ∈ U
  rwa [fieldPt_apply]

theorem fieldPt_appLE {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) ≫ (Scheme.ΓSpecIso (.of L)).hom = X.presheaf.germ U _ hU ≫ φ := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := fun x _ => by
    letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have : x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
    change X.fromSpecStalk _ x ∈ U
    rw [this, Scheme.fromSpecStalk_closedPoint]
    exact hU
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) (X.fromSpecStalk (genericPoint X)) U ⊤ ⊤ h1 le_rfl]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ le_rfl = (Spec.map φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [h2, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  have h3 : ∀ i : (Opposite.op ⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opensᵒᵖ) ⟶ Opposite.op ⊤,
      (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map i = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
  rw [h3]
  simp

def normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    Γ((fieldPt φ).normalization, (fieldPt φ).fromNormalization ⁻¹ᵁ U) ⟶ .of L :=
  (fieldPt φ).toNormalization.appLE _ ⊤ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU) ≫
    (Scheme.ΓSpecIso (.of L)).hom

theorem app_normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).fromNormalization.app U ≫ normFun φ hU = X.presheaf.germ U _ hU ≫ φ := by
  have key : ∀ (g : Spec (.of L) ⟶ X) (_ : g = fieldPt φ) (e : ⊤ ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) := by
    rintro _ rfl _
    rfl
  rw [normFun, ← fieldPt_appLE, ← Category.assoc]
  congr 1
  exact (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans (key _ (fieldPt φ).toNormalization_fromNormalization (by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU))

theorem normFun_spec {U : X.Opens} (hU : genericPoint X ∈ U) (hA : IsAffineOpen U) :
    Function.Injective (normFun φ hU).hom ∧
      ∀ x : L, x ∈ (normFun φ hU).hom.range ↔ (X.presheaf.germ U _ hU ≫ φ).hom.IsIntegralElem x := by
  let u := fieldPt φ
  letI := (u.app U).hom.toAlgebra
  let ε : Γ(Spec (.of L), u ⁻¹ᵁ U) ⟶ .of L :=
    (Spec (.of L)).presheaf.map (homOfLE (top_le_fieldPt φ hU)).op ≫ (Scheme.ΓSpecIso (.of L)).hom
  have hε : Function.Bijective ε.hom := by
    have : homOfLE (top_le_fieldPt φ hU) = eqToHom (top_le_iff.1 (top_le_fieldPt φ hU)).symm := Subsingleton.elim _ _
    haveI : IsIso ε := by
      simp only [ε, this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ε
  have h1 : normFun φ hU = (u.normalizationObjIso hA).hom ≫
      CommRingCat.ofHom (integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U)).val.toRingHom ≫ ε := by
    rw [← Category.assoc, u.normalizationObjIso_hom_val hA, normFun]
    simp only [ε]
    rw [Scheme.Hom.appLE_map_assoc]
  have h2 : X.presheaf.germ U _ hU ≫ φ = u.app U ≫ ε := by
    rw [← fieldPt_appLE, Scheme.Hom.appLE, Category.assoc]
  have hb := ConcreteCategory.bijective_of_isIso (u.normalizationObjIso hA).hom
  rw [h1, h2]
  refine ⟨hε.1.comp (Subtype.val_injective.comp hb.1), fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp, hp0⟩ := ((u.normalizationObjIso hA).hom y).2
    refine ⟨p, hp, ?_⟩
    have := congrArg ε.hom hp0
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  · rintro ⟨p, hp, hp0⟩
    obtain ⟨y, rfl⟩ := hε.2 x
    have hy : IsIntegral Γ(X, U) y := ⟨p, hp, hε.1 (by rw [Polynomial.hom_eval₂, map_zero]; exact hp0)⟩
    obtain ⟨z, hz⟩ := hb.2 ⟨y, hy⟩
    exact ⟨z, congrArg (fun w : integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U) => ε.hom w.1) hz⟩

end Field

end GlobalTheory.BplusDescent

end
