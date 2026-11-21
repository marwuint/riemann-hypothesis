import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Cech

variable {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

theorem map_ev (f : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (i : V' ≤ V)
    (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE i).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (i.trans e)).hom x :=
  congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, V') => φ.hom x) (f.appLE_map e (homOfLE i).op)

theorem ev_map (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (i : U ≤ U')
    (e' : V ≤ f ⁻¹ᵁ U') (x : Γ(X, U')) :
    (f.appLE U V e).hom ((X.presheaf.map (homOfLE i).op).hom x) = (f.appLE U' V e').hom x :=
  congrArg (fun φ : Γ(X, U') ⟶ Γ(Y, V) => φ.hom x) (f.map_appLE e (homOfLE i).op)

theorem ev_ev (f : Z ⟶ Y) (g : Y ⟶ X) (k : Z ⟶ X) (hk : f ≫ g = k) {U : X.Opens} {V : Y.Opens}
    {W : Z.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ k ⁻¹ᵁ U) (x : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (k.appLE U W e₃).hom x := by
  subst hk
  exact congrArg (fun φ : Γ(X, U) ⟶ Γ(Z, W) => φ.hom x)
    (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem transition_pull (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X))
    (hφ : ∀ k, h ≫ φ k = φ' k) (j j' : K → L.ι)
    (e : LB.wchart L φ' j ⊓ LB.wchart L φ' j' ≤ h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    (h.appLE _ _ e).hom
      (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j') from ((LB.LinComb L φ ε).g j j').val) =
      (show Γ(Z, LB.wchart L φ' j ⊓ LB.wchart L φ' j') from ((LB.LinComb L φ' ε).g j j').val) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext fun k => (hφ k).symm
  have key : Units.map (h.appLE _ _ e).hom.toMonoidHom ((LB.LinComb L φ ε).g j j') =
      (LB.LinComb L (fun k => h ≫ φ k) ε).g j j' := by
    simp only [LB.LinComb, map_prod, map_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    ext
    exact ev_ev h (φ k) _ rfl (U := L.U (j k) ⊓ L.U (j' k))
      (le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k)))
      e (le_inf (inf_le_left.trans (LB.wchart_le L (fun k => h ≫ φ k) j k))
        (inf_le_right.trans (LB.wchart_le L (fun k => h ≫ φ k) j' k))) (L.g (j k) (j' k)).val
  exact congrArg Units.val key

end Cech

section Sections

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def Secs (L : LB A.left) (a : ℤ) (T : Over S) : Type := LB.Sec (LPow A L a T)

variable {A} {L : LB A.left} {a : ℤ} {T : Over S}

theorem Secs.ext {s t : Secs A L a T} (h : ∀ j, LB.Sec.f s j = LB.Sec.f t j) : s = t := by
  cases s; cases t; congr; exact funext h

theorem liftFun_eq {T : Over S} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) :
    liftFun A W r = ((fst T A).left.appLE ⊤ W le_top).hom r := rfl

theorem map_liftFun {W W' : (T ⊗ A).left.Opens} (e : W' ≤ W) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE e).op).hom (liftFun A W r) = liftFun A W' r :=
  map_ev (fst T A).left le_top e r

instance : Zero (Secs A L a T) := ⟨⟨fun _ => 0, fun _ _ => by simp⟩⟩
instance : Add (Secs A L a T) :=
  ⟨fun s t => ⟨fun j => s.f j + t.f j, fun i j => by
    rw [map_add, map_add, s.compat i j, t.compat i j, mul_add]⟩⟩
instance : Neg (Secs A L a T) :=
  ⟨fun s => ⟨fun j => - s.f j, fun i j => by rw [map_neg, map_neg, s.compat i j, mul_neg]⟩⟩
instance : SMul Γ(T.left, ⊤) (Secs A L a T) :=
  ⟨fun r s => ⟨fun j => liftFun A _ r * s.f j, fun i j => by
    rw [map_mul, map_mul, map_liftFun, map_liftFun, s.compat i j, mul_left_comm]⟩⟩

theorem zero_f (j) : LB.Sec.f (0 : Secs A L a T) j = 0 := rfl
theorem add_f (s t : Secs A L a T) (j) : LB.Sec.f (s + t) j = LB.Sec.f s j + LB.Sec.f t j := rfl
theorem neg_f (s : Secs A L a T) (j) : LB.Sec.f (-s) j = - LB.Sec.f s j := rfl
theorem smul_f (r : Γ(T.left, ⊤)) (s : Secs A L a T) (j) :
    LB.Sec.f (r • s) j = liftFun A _ r * LB.Sec.f s j := rfl

instance : AddCommGroup (Secs A L a T) where
  add_assoc s t u := Secs.ext fun j => add_assoc _ _ _
  zero_add s := Secs.ext fun j => zero_add _
  add_zero s := Secs.ext fun j => add_zero _
  add_comm s t := Secs.ext fun j => add_comm _ _
  neg_add_cancel s := Secs.ext fun j => neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module Γ(T.left, ⊤) (Secs A L a T) where
  one_smul s := Secs.ext fun j => by rw [smul_f, liftFun_eq, map_one, _root_.one_mul]
  mul_smul r r' s := Secs.ext fun j => by
    rw [smul_f, smul_f, smul_f, liftFun_eq, liftFun_eq, liftFun_eq, map_mul, _root_.mul_assoc]
  smul_zero r := Secs.ext fun j => mul_zero _
  smul_add r s t := Secs.ext fun j => mul_add _ _ _
  add_smul r r' s := Secs.ext fun j => by
    rw [add_f, smul_f, smul_f, smul_f, liftFun_eq, liftFun_eq, liftFun_eq, map_add, add_mul]
  zero_smul s := Secs.ext fun j => by rw [smul_f, liftFun_eq, map_zero, zero_mul, zero_f]

def pullSec {T' : Over S} (u : T' ⟶ T) (s : Secs A L a T) : Secs A L a T' where
  f j := ((u ▷ A).left.appLE _ _ (chart_le_res A L (u ▷ A) (whiskerRight_snd _ _) a j)).hom (s.f j)
  compat i j := by
    have e : (LPow A L a T').U i ⊓ (LPow A L a T').U j ≤
        (u ▷ A).left ⁻¹ᵁ ((LPow A L a T).U i ⊓ (LPow A L a T).U j) :=
      inf_le_inf (chart_le_res A L (u ▷ A) (whiskerRight_snd _ _) a i)
        (chart_le_res A L (u ▷ A) (whiskerRight_snd _ _) a j)
    have h := congrArg ((u ▷ A).left.appLE _ _ e).hom (s.compat i j)
    rw [map_mul] at h
    have hg := transition_pull L (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (u ▷ A).left
      (fun _ => (snd T' A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd]) i j e
    refine (map_ev _ _ _ _).trans ((ev_map _ e _ _ _).symm.trans (h.trans ?_))
    exact congrArg₂ (· * ·) hg ((ev_map _ e _ _ _).trans (map_ev _ _ _ _).symm)

end Sections

variable {S : Scheme.{0}}

end GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
