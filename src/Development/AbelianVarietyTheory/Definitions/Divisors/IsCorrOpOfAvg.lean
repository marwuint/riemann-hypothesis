import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

variable (l : ℕ) [Fact l.Prime]

abbrev Htot (E : Spc) : Type 1 := DirectSum ℤ fun n : ℤ => HQ l E n 0

def pullTot {E E' : Spc} (f : E ⟶ E') : Htot l E' →ₗ[ℚ_[l]] Htot l E :=
  DirectSum.lmap fun n => pullHQ l f n 0

theorem pullTot_id (E : Spc) : pullTot l (𝟙 E) = LinearMap.id := by
  simp only [pullTot, pullHQ, pullHl_id, LinearMap.baseChange_id]
  exact DirectSum.lmap_id

theorem pullTot_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') :
    pullTot l (f ≫ g) = pullTot l f ∘ₗ pullTot l g := by
  simp only [pullTot, pullHQ, pullHl_comp, LinearMap.baseChange_comp]
  exact DirectSum.lmap_comp _ _

def galTot {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    (Ω ≃ₐ[k] Ω) → Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) →ₗ[ℚ_[l]] Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) :=
  fun σ => pullTot l (sch.map (GlobalTheory.Et.galMap Ω p σ))

private theorem galMap_one' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : GlobalTheory.Et.galMap Ω p (1 : Ω ≃ₐ[k] Ω) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.id_comp]
  · rw [GlobalTheory.Et.galMap_snd, Category.id_comp]
    have h1 : CommRingCat.ofHom ((1 : Ω ≃ₐ[k] Ω) : Ω →+* Ω) = 𝟙 _ := by
      ext x; rfl
    rw [h1, Spec.map_id, Category.comp_id]

theorem galTot_one {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    galTot l Ω p 1 = LinearMap.id := by
  simp only [galTot]
  rw [galMap_one', CategoryTheory.Functor.map_id, pullTot_id]

private theorem galMap_mul' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ τ : Ω ≃ₐ[k] Ω) :
    GlobalTheory.Et.galMap Ω p (σ * τ) = GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.galMap Ω p τ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.assoc, GlobalTheory.Et.galMap_fst, GlobalTheory.Et.galMap_fst]
  · have h2 : CommRingCat.ofHom ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →+* Ω) =
        CommRingCat.ofHom (τ : Ω →+* Ω) ≫ CommRingCat.ofHom (σ : Ω →+* Ω) := by
      ext x; rfl
    rw [GlobalTheory.Et.galMap_snd, Category.assoc, GlobalTheory.Et.galMap_snd, GlobalTheory.Et.galMap_snd_assoc, h2, Spec.map_comp]

theorem galTot_mul {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (σ τ : Ω ≃ₐ[k] Ω) : galTot l Ω p (σ * τ) = galTot l Ω p σ ∘ₗ galTot l Ω p τ := by
  simp only [galTot]
  rw [galMap_mul', CategoryTheory.Functor.map_comp, pullTot_comp]

def galTotRep {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (Htot l (sch.obj (GlobalTheory.Et.geom Ω p))) where
  toFun := galTot l Ω p
  map_one' := galTot_one l Ω p
  map_mul' := galTot_mul l Ω p

def Splits {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) {J : Type} (σ : J → (W ⟶ Y)) : Prop :=
  ∃ h : ∀ j, σ j ≫ s = c,
    IsIso (Limits.Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s c)

def IsGalois {W X : Scheme.{0}} (c : W ⟶ X) (G : Type) [Group G] (a : G → (W ⟶ W)) : Prop :=
  IsFinite c ∧ Etale c ∧ Surjective c ∧ a 1 = 𝟙 W ∧ (∀ g h, a (g * h) = a g ≫ a h) ∧ Splits c c a

def IsCorrOp {Z Y Z' : Scheme.{0}} (s : Y ⟶ Z) (t : Y ⟶ Z') (T : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) : Prop :=
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (J : Type) (_ : Fintype J)
    (σ : J → (W ⟶ Y)), IsGalois c G a ∧ Splits s c σ ∧
    ∀ x, pullTot l (sch.map c) (T x) = ∑ j, pullTot l (sch.map (σ j ≫ t)) x

variable {l}

def genEig {H : Type*} [AddCommGroup H] [Module ℚ_[l] H] (L : Type*) [Field L] [Algebra ℚ_[l] L] {J : Type*}
    (T : J → H →ₗ[ℚ_[l]] H) (θ : J → L) : Submodule L (TensorProduct ℚ_[l] L (H)) :=
  ⨅ j, Module.End.maxGenEigenspace ((T j).baseChange L) (θ j)

variable (l)

end GlobalTheory.GalV

end
