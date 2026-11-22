import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite TensorProduct

universe u

noncomputable section

namespace GlobalTheory.StalkProd

variable {X : Scheme.{u}}

def homMk {F G : X.Modules} (φ : ∀ U : X.Opens, Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U))
    (hφ : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)),
      φ V (F.presheaf.map i.op s) = G.presheaf.map i.op (φ U s)) : F ⟶ G :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (φ U.unop).toAddMonoidHom
      naturality := fun _ _ i => by
        ext s
        exact hφ i.unop s }
    (fun U r m => (φ U.unop).map_smul r m)

@[simp] theorem homMk_app {F G : X.Modules} (φ : ∀ U : X.Opens, Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U))
    (hφ : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)),
      φ V (F.presheaf.map i.op s) = G.presheaf.map i.op (φ U s)) (U : X.Opens) (s : Γ(F, U)) :
    (homMk φ hφ).app U s = φ U s := rfl

section Pi

variable (E : X → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module (X.presheaf.stalk x) (E x)]

def presheafAb : TopCat.Presheaf Ab.{u} X where
  obj U := AddCommGrpCat.of (∀ x : U.unop, E x)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s x => s ⟨x.1, i.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem isSheaf_presheafAb : (presheafAb E).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget Ab.{u})]
  exact TopCat.Presheaf.toTypes_isSheaf X E

abbrev secModule (U : X.Opens) : Module Γ(X, U) (∀ x : U, E x) :=
  @Pi.module U (fun x : U => E x.1) Γ(X, U) _ _ fun x => Module.compHom (E x.1) (X.presheaf.germ U x.1 x.2).hom

def pi : X.Modules :=
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((presheafAb E).obj U) :=
    fun U => secModule E U.unop
  { val := PresheafOfModules.ofPresheaf (presheafAb E) fun U V i r s => by
      funext x
      show X.presheaf.germ U.unop x.1 _ r • s ⟨x.1, i.unop.le x.2⟩ =
        X.presheaf.germ V.unop x.1 x.2 (X.presheaf.map i r) • s ⟨x.1, i.unop.le x.2⟩
      rw [← Quiver.Hom.op_unop i, X.presheaf.germ_res_apply i.unop x.1 x.2 r]
    isSheaf := isSheaf_presheafAb E }

variable {E}

def fam {U : X.Opens} (s : Γ(pi E, U)) : ∀ x : U, E x := s

def mk {U : X.Opens} (s : ∀ x : U, E x) : Γ(pi E, U) := s

@[simp] theorem fam_mk {U : X.Opens} (s : ∀ x : U, E x) : fam (mk s) = s := rfl

@[simp] theorem fam_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(pi E, U)) (x : U) :
    fam (r • s) x = X.presheaf.germ U x.1 x.2 r • fam s x := rfl

@[simp] theorem fam_add {U : X.Opens} (s t : Γ(pi E, U)) (x : U) :
    fam (s + t) x = fam s x + fam t x := rfl

@[simp] theorem fam_zero {U : X.Opens} (x : U) : fam (0 : Γ(pi E, U)) x = 0 := rfl

@[simp] theorem fam_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(pi E, U)) (x : V) :
    fam ((pi E).presheaf.map i.op s) x = fam s ⟨x.1, i.le x.2⟩ := rfl

variable {E' : X → Type u} [∀ x, AddCommGroup (E' x)] [∀ x, Module (X.presheaf.stalk x) (E' x)]

def piMap (L : ∀ x, E x →ₗ[X.presheaf.stalk x] E' x) : pi E ⟶ pi E' :=
  homMk (fun U =>
    { toFun := fun s => mk fun x => L x.1 (fam s x)
      map_add' := fun s t => funext fun x => map_add (L x.1) _ _
      map_smul' := fun r s => funext fun x => (L x.1).map_smul _ _ })
    fun _ _ => rfl

@[simp] theorem fam_piMap_app (L : ∀ x, E x →ₗ[X.presheaf.stalk x] E' x) {U : X.Opens}
    (s : Γ(pi E, U)) (x : U) : fam ((piMap L).app U s) x = L x.1 (fam s x) := rfl

end Pi

def germs (F : X.Modules) : F ⟶ pi (fun x => (F.presheaf.stalk x : Type u)) :=
  homMk (fun U =>
    { toFun := fun s => mk fun x => F.presheaf.germ U x.1 x.2 s
      map_add' := fun s t => funext fun x => map_add _ _ _
      map_smul' := fun r s => funext fun x => QCoh.germ_smul F x.1 x.2 r s })
    fun i s => funext fun x => F.presheaf.germ_res_apply i x.1 x.2 s

@[simp] theorem fam_germs_app (F : X.Modules) {U : X.Opens} (s : Γ(F, U)) (x : U) :
    fam ((germs F).app U s) x = F.presheaf.germ U x.1 x.2 s := rfl

section Tensor

variable {Y : Scheme.{u}} (f : X ⟶ Y)

abbrev stalkAlgebra (x : X) : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

attribute [local instance] stalkAlgebra

variable (M : Y.Modules)

def tensorStalk (x : X) : Type u :=
  X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] (M.presheaf.stalk (f x) : Type u)

instance (x : X) : AddCommGroup (tensorStalk f M x) :=
  inferInstanceAs (AddCommGroup (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
    (M.presheaf.stalk (f x) : Type u)))

instance (x : X) : Module (X.presheaf.stalk x) (tensorStalk f M x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
    (M.presheaf.stalk (f x) : Type u)))

variable {M} {M' : Y.Modules}

end Tensor

end GlobalTheory.StalkProd
