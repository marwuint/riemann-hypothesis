import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomZeroEquivSections

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

structure RActPre (X : Scheme.{0}) (Γ : Type) [Group Γ] where

  P : (Over X)ᵒᵖ ⥤ Type

  act : Γ → (P ⟶ P)
  act_one : act 1 = 𝟙 P
  act_mul : ∀ g h, act (g * h) = act g ≫ act h

variable {X : Scheme.{0}} (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

def assocSet (Q : RActPre X Γ) (ξ : Γ →* GL ι E) (T : Over X) :
    Submodule E (∀ (T' : Over X) (_ : T' ⟶ T) (_ : Q.P.obj (op T')), C(T'.left, ι → E)) where
  carrier := {f | (∀ ⦃T'' T' : Over X⦄ (v : T'' ⟶ T') (u : T' ⟶ T) (η : Q.P.obj (op T')) (t : T''.left),
      f T'' (v ≫ u) (Q.P.map v.op η) t = f T' u η (v.left.base t)) ∧
    ∀ ⦃T' : Over X⦄ (u : T' ⟶ T) (η : Q.P.obj (op T')) (γ : Γ) (t : T'.left),
      f T' u ((Q.act γ).app (op T') η) t = ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ f T' u η t}
  add_mem' {f g} hf hg := ⟨fun T'' T' v u η t => by
      simp only [Pi.add_apply, ContinuousMap.add_apply, hf.1 v u η t, hg.1 v u η t],
    fun T' u η γ t => by
      simp only [Pi.add_apply, ContinuousMap.add_apply, hf.2 u η γ t, hg.2 u η γ t, Matrix.mulVec_add]⟩
  zero_mem' := ⟨fun _ _ _ _ _ _ => rfl, fun T' u η γ t => by simp⟩
  smul_mem' c {f} hf := ⟨fun T'' T' v u η t => by
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, hf.1 v u η t],
    fun T' u η γ t => by
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, hf.2 u η γ t, Matrix.mulVec_smul]⟩

def assocRes (Q : RActPre X Γ) (ξ : Γ →* GL ι E) {T₁ T₂ : Over X} (w : T₁ ⟶ T₂) :
    assocSet E Q ξ T₂ →ₗ[E] assocSet E Q ξ T₁ where
  toFun f := ⟨fun T' u η => f.1 T' (u ≫ w) η,
    ⟨fun T'' T' v u η t => by simpa only [Category.assoc] using f.2.1 v (u ≫ w) η t,
      fun T' u η γ t => f.2.2 (u ≫ w) η γ t⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def assocPre (Q : RActPre X Γ) (ξ : Γ →* GL ι E) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} E) where
  obj T := ModuleCat.of (ULift.{1} E) (assocSet E Q ξ T.unop)
  map w := ModuleCat.ofHom
    { toFun := assocRes E Q ξ w.unop
      map_add' := (assocRes E Q ξ w.unop).map_add
      map_smul' := fun r f => (assocRes E Q ξ w.unop).map_smul r.down f }
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun f => Subtype.ext (funext fun T' => funext fun u =>
    funext fun η => by
      change f.1 T' (u ≫ 𝟙 _) η = f.1 T' u η
      rw [Category.comp_id]))
  map_comp w₁ w₂ := ModuleCat.hom_ext (LinearMap.ext fun f => Subtype.ext (funext fun T' => funext fun u =>
    funext fun η => by
      change f.1 T' (u ≫ (w₂.unop ≫ w₁.unop)) η = f.1 T' ((u ≫ w₂.unop) ≫ w₁.unop) η
      rw [Category.assoc]))

abbrev cPre (X : Scheme.{0}) (ι : Type) : (Over X)ᵒᵖ ⥤ Type :=
  (Over.forget X).op ⋙ continuousMapPresheaf.{0} (ι → E)

theorem cPre_isSheaf (X : Scheme.{0}) (ι : Type) :
    Presieve.IsSheaf (Scheme.proetaleTopology.{0}.over X) (cPre E X ι) := by
  have h0 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} (ι → E)) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf _)
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (CategoryTheory.Sheaf.over (⟨_, h0⟩ : Sheaf Scheme.proetaleTopology.{0} Type) X).cond

section
variable {E} (Q : RActPre X Γ) (ξ : Γ →* GL ι E)

theorem assocSet_nat {T : Over X} (f : assocSet E Q ξ T) {T'' T' : Over X} (v : T'' ⟶ T') (u : T' ⟶ T)
    (η : Q.P.obj (op T')) :
    f.1 T'' (v ≫ u) (Q.P.map v.op η) = (cPre E X ι).map v.op (f.1 T' u η) :=
  ContinuousMap.ext fun t => f.2.1 v u η t

end

theorem assocPre_isSheaf (Q : RActPre X Γ) (ξ : Γ →* GL ι E) :
    Presheaf.IsSheaf (Scheme.proetaleTopology.{0}.over X) (assocPre E Q ξ) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _), isSheaf_iff_isSheaf_of_type]
  intro T S hS x hx
  have hC := cPre_isSheaf E X ι
  let xv : ∀ ⦃Y : Over X⦄ (f : Y ⟶ T), S f → assocSet E Q ξ Y := fun Y f h => x f h

  have K : ∀ ⦃Y₁ Y₂ Z : Over X⦄ (f₁ : Y₁ ⟶ T) (f₂ : Y₂ ⟶ T) (h₁ : S f₁) (h₂ : S f₂) (a₁ : Z ⟶ Y₁) (a₂ : Z ⟶ Y₂),
      a₁ ≫ f₁ = a₂ ≫ f₂ → ∀ η, (xv f₁ h₁).1 Z a₁ η = (xv f₂ h₂).1 Z a₂ η := by
    intro Y₁ Y₂ Z f₁ f₂ h₁ h₂ a₁ a₂ e η
    have := hx a₁ a₂ h₁ h₂ e
    have h := congrArg (fun z => (show assocSet E Q ξ Z from z).1 Z (𝟙 Z) η) this
    change (xv f₁ h₁).1 Z (𝟙 Z ≫ a₁) η = (xv f₂ h₂).1 Z (𝟙 Z ≫ a₂) η at h
    simpa only [Category.id_comp] using h
  let fam : ∀ (T' : Over X) (_ : T' ⟶ T) (_ : Q.P.obj (op T')),
      Presieve.FamilyOfElements (cPre E X ι) (S.pullback ‹T' ⟶ T›).arrows := fun T' u η Y w hw =>
    (xv (w ≫ u) hw).1 Y (𝟙 Y) (Q.P.map w.op η)
  have famC : ∀ T' u η, (fam T' u η).Compatible := by
    intro T' u η Y₁ Y₂ Z g₁ g₂ w₁ w₂ hw₁ hw₂ e
    change (cPre E X ι).map g₁.op ((xv (w₁ ≫ u) hw₁).1 Y₁ (𝟙 Y₁) (Q.P.map w₁.op η)) =
      (cPre E X ι).map g₂.op ((xv (w₂ ≫ u) hw₂).1 Y₂ (𝟙 Y₂) (Q.P.map w₂.op η))
    rw [← assocSet_nat, ← assocSet_nat, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, e]
    exact K _ _ _ _ _ _ (by simp only [Category.comp_id, ← Category.assoc, e]) _
  let gl : ∀ (T' : Over X) (u : T' ⟶ T) (η : Q.P.obj (op T')), C(T'.left, ι → E) := fun T' u η =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).amalgamate (fam T' u η) (famC T' u η)
  have glv : ∀ T' (u : T' ⟶ T) η ⦃Y : Over X⦄ (w : Y ⟶ T') (hw : S (w ≫ u)),
      (cPre E X ι).map w.op (gl T' u η) = (xv (w ≫ u) hw).1 Y (𝟙 Y) (Q.P.map w.op η) := fun T' u η Y w hw =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).valid_glue (famC T' u η) w hw
  have sep : ∀ (T' : Over X) (u : T' ⟶ T) (c₁ c₂ : C(T'.left, ι → E)),
      (∀ ⦃Y : Over X⦄ (w : Y ⟶ T'), S (w ≫ u) → (cPre E X ι).map w.op c₁ = (cPre E X ι).map w.op c₂) →
        c₁ = c₂ := fun T' u c₁ c₂ h =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).isSeparatedFor.ext fun Y w hw => h w hw
  have mem : (fun T' u η => gl T' u η) ∈ assocSet E Q ξ T := by
    refine ⟨fun T'' T' v u η t => ?_, fun T' u η γ t => ?_⟩
    · have H : gl T'' (v ≫ u) (Q.P.map v.op η) = (cPre E X ι).map v.op (gl T' u η) := by
        refine sep T'' (v ≫ u) _ _ fun Y w hw => ?_
        rw [glv _ _ _ w hw, ← Functor.map_comp_apply (cPre E X ι), ← op_comp,
          glv T' u η (w ≫ v) (by simpa only [Category.assoc] using hw), op_comp, Functor.map_comp_apply]
        exact K _ _ _ _ _ _ (by simp only [Category.assoc]) _
      exact DFunLike.congr_fun H t
    · let M : ∀ Z : Over X, C(Z.left, ι → E) → C(Z.left, ι → E) := fun Z c =>
        ⟨fun t => ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ c t, continuous_const.matrix_mulVec c.continuous⟩
      have hM : ∀ c t, M T' c t = ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ c t := fun _ _ => rfl
      have hMn : ∀ ⦃Y⦄ (w : Y ⟶ T') c, (cPre E X ι).map w.op (M T' c) = M Y ((cPre E X ι).map w.op c) :=
        fun _ _ _ => rfl
      rw [← hM]
      have H : gl T' u ((Q.act γ).app (op T') η) = M T' (gl T' u η) := by
        refine sep T' u _ _ fun Y w hw => ?_
        rw [glv _ _ _ w hw, hMn, glv _ _ _ w hw]
        have hn : Q.P.map w.op ((Q.act γ).app (op T') η) = (Q.act γ).app (op Y) (Q.P.map w.op η) :=
          (NatTrans.naturality_apply (Q.act γ) w.op η).symm
        rw [hn]
        exact ContinuousMap.ext fun t => (xv (w ≫ u) hw).2.2 (𝟙 Y) _ γ t
      exact DFunLike.congr_fun H t
  refine ⟨⟨_, mem⟩, ?_, ?_⟩
  · intro Y f hf
    apply Subtype.ext
    funext Y' u η
    change gl Y' (u ≫ f) η = (xv f hf).1 Y' u η
    refine sep Y' (u ≫ f) _ _ fun Z w hw => ?_
    rw [glv _ _ _ w hw, ← assocSet_nat]
    exact K _ _ _ _ _ _ (by simp only [Category.id_comp, Category.assoc]) _
  · intro t' ht'
    apply Subtype.ext
    funext T' u η
    have ht : ∀ ⦃Y : Over X⦄ (f : Y ⟶ T) (hf : S f) η', (show assocSet E Q ξ T from t').1 Y (𝟙 Y ≫ f) η' =
        (xv f hf).1 Y (𝟙 Y) η' := fun Y f hf η' =>
      congrArg (fun z => (show assocSet E Q ξ Y from z).1 Y (𝟙 Y) η') (ht' f hf)
    change (show assocSet E Q ξ T from t').1 T' u η = gl T' u η
    refine sep T' u _ _ fun Y w hw => ?_
    rw [glv _ _ _ w hw, ← assocSet_nat, ← ht _ hw, Category.id_comp]

def assoc (Q : RActPre X Γ) (ξ : Γ →* GL ι E) : Shv E X := ⟨assocPre E Q ξ, assocPre_isSheaf E Q ξ⟩

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

end GlobalTheory.Et.Rel
