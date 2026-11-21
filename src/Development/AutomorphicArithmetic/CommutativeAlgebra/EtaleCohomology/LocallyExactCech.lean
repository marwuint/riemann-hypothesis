import Mathlib

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Et

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

abbrev PC (R : Type) [CommRing R] : Type 2 := CochainComplex (PMod R) ℤ

variable {R : Type} [CommRing R]

abbrev sec (M : PMod R) (U : Scheme.{0}) : Type 1 := M.obj (op U)

abbrev rs (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (x : sec M U) : sec M V := (M.map g.op).hom x

abbrev ap {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} (x : sec M U) : sec N U := (α.app (op U)).hom x

def LocT (τ : GrothendieckTopology Scheme.{0}) (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ τ U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

def IsCy (K : PC R) (n : ℤ) {U : Scheme.{0}} (z : sec (K.X n) U) : Prop := ap (K.d n (n + 1)) z = 0

def IsBd (K : PC R) (n : ℤ) {U : Scheme.{0}} (z : sec (K.X n) U) : Prop := ∃ y : sec (K.X (n - 1)) U, ap (K.d (n - 1) n) y = z

def Inv (q : ℕ) (U : Scheme.{0}) : Prop := IsUnit (q : Γ(U, ⊤))

structure Model (K : PC R) (n : ℤ) (H : Scheme.{0} → Type 1) [∀ X, AddCommGroup (H X)]
    (pull : ∀ {Y X : Scheme.{0}}, (Y ⟶ X) → H X → H Y) (rel : ∀ X : Scheme.{0}, sec (K.X n) X → H X → Prop) : Prop where
  ex : ∀ X z, IsCy K n z → ∃ y, rel X z y
  surj : ∀ X y, ∃ z, rel X z y
  cyc : ∀ X z y, rel X z y → IsCy K n z
  sub : ∀ X z y z' y', rel X z y → rel X z' y' → rel X (z - z') (y - y')
  zero : ∀ X z y, rel X z y → (y = 0 ↔ IsBd K n z)
  nat : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) z y, rel X z y → rel Y (rs _ f z) (pull f y)

def Gen (τ : GrothendieckTopology Scheme.{0}) (q : ℕ) (M : PMod R) {U : Scheme.{0}} (g : sec M U) : Prop :=
  q • g = 0 ∧ (∀ (V : Scheme.{0}) (k : V ⟶ U) (c : ℕ), Nonempty V → c • rs M k g = 0 → q ∣ c) ∧
  ∀ (V : Scheme.{0}) (k : V ⟶ U) (y : sec M V), LocT τ V fun _ h => ∃ c : ℕ, rs M h y = c • rs M (h ≫ k) g

section Cech
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

@[ext] structure Pt {U : Scheme.{0}} (π : U ⟶ X) (p : ℕ) (W : Scheme.{0}) : Type where
  u : W ⟶ U
  y : Fin p → (W ⟶ Y)
  w : ∀ i, y i ≫ f = u ≫ π

variable {f} in

def Pt.pre {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} {W' W : Scheme.{0}} (k : W' ⟶ W) (x : Pt f π p W) : Pt f π p W' :=
  ⟨k ≫ x.u, fun i => k ≫ x.y i, fun i => by rw [Category.assoc, x.w i, Category.assoc]⟩

variable {f} in

def Pt.face {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} {W : Scheme.{0}} (x : Pt f π (p + 1) W) (i : Fin (p + 1)) : Pt f π p W :=
  ⟨x.u, fun j => x.y (i.succAbove j), fun _ => x.w _⟩

def Cc (M : PMod R) {U : Scheme.{0}} (π : U ⟶ X) (p : ℕ) : AddSubgroup (∀ W : Scheme.{0}, Pt f π p W → sec M W) where
  carrier := {c | ∀ (W' W : Scheme.{0}) (k : W' ⟶ W) (x : Pt f π p W), rs M k (c W x) = c W' (x.pre k)}
  zero_mem' _ _ _ _ := map_zero _
  add_mem' {a b} ha hb W' W k x := (map_add _ _ _).trans (congrArg₂ (· + ·) (ha W' W k x) (hb W' W k x))
  neg_mem' {a} ha W' W k x := (map_neg _ _).trans (congrArg Neg.neg (ha W' W k x))

variable {f}

def Cc.map {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} : Cc f M π p →+ Cc f N π p where
  toFun c := ⟨fun W x => ap α (c.1 W x), by
    intro W' W k x
    change _ = ap α (c.1 W' (x.pre k))
    rw [← c.2 W' W k x]
    exact (ConcreteCategory.congr_hom (α.naturality k.op) (c.1 W x)).symm⟩
  map_zero' := by ext W x; simp
  map_add' a b := by ext W x; simp

variable (f)

end Cech

end UpperTheory.Et

end
