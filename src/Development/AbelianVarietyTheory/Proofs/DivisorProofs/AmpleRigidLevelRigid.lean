import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.RealMult

set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]
    (f : G' ⟶ G) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have H := h.2 T x y
  revert H
  generalize hg : T.hom ≫ 𝟙 S = g
  rw [Category.comp_id] at hg
  subst hg
  intro H
  exact Over.OverMorphism.ext (H (x ≫ f) (y ≫ f) rfl rfl).symm

set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AmpleRigid.isMonHom_of_mul_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (e : G ⟶ H) (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
    IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h1 := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h1
    exact _root_.left_eq_mul.mp h1
  refine ⟨?_, ?_⟩
  · simpa [Hom.one_def] using hone
  · have h2 := mul (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using h2

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem pull_cls_diag {S : Scheme.{0}} (X : Obj F 𝔠 S) (ψ : X.A.left ⟶ X.A.left) (hψ : X.IsPullBy X (𝟙 _) ψ)
    (c : 𝔠.elt) :
    pull ψ (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag c) (pull_isLB (X.isLB c) _) := by
  obtain ⟨φ₂, hsq, hiso⟩ := hψ.pol
  have hw : ψ ≫ X.A.hom = X.A.hom := by simpa using hψ.grp.1.w
  have hw2 : φ₂ ≫ (X.A ⊗ X.A).hom = (X.A ⊗ X.A).hom := by
    calc φ₂ ≫ (X.A ⊗ X.A).hom = φ₂ ≫ (fst X.A X.A).left ≫ X.A.hom := by rw [Over.w]
      _ = (fst X.A X.A).left ≫ ψ ≫ X.A.hom := by rw [← Category.assoc, hsq.1, Category.assoc]
      _ = (X.A ⊗ X.A).hom := by rw [hw, Over.w]
  let Ψ : X.A ⟶ X.A := Over.homMk ψ hw
  let Φ : X.A ⊗ X.A ⟶ X.A ⊗ X.A := Over.homMk φ₂ hw2
  have e : Ψ ≫ lift (𝟙 X.A) (𝟙 X.A) = lift (𝟙 X.A) (𝟙 X.A) ≫ Φ := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_fst, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      rfl
    · apply Over.OverMorphism.ext
      simp only [Category.assoc, lift_snd, Category.comp_id, Over.comp_left]
      rw [show Φ.left = φ₂ from rfl, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have e' : ψ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left = (lift (𝟙 X.A) (𝟙 X.A)).left ≫ φ₂ := congrArg (·.left) e
  have h1 : pull φ₂ (cls (X.P c) (X.isLB c)) = cls (X.P c) (X.isLB c) :=
    ((cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hiso c)).symm
  unfold Obj.diag
  rw [cls_pull (X.isLB c), ← pull_comp, e', pull_comp, h1]

end GlobalTheory.AmpleRigid
