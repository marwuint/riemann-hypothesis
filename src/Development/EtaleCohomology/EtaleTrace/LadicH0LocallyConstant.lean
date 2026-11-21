import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace

abbrev S (k : Type) [Field k] : Scheme.{0} := Spec (CommRingCat.of k)

section Defs
variable (l : ℕ) [Fact l.Prime]

abbrev V (X : Scheme.{0}) (n : ℤ) : Type 1 := HQ l (sch.obj X) n 0

abbrev pb {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℤ) : V l X n →ₗ[ℚ_[l]] V l Y n := pullHQ l (sch.map f) n 0

def IsCup (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) (c : V l X n →ₗ[ℚ_[l]] V l X m →ₗ[ℚ_[l]] V l X r) : Prop :=
  ∀ (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj X) m 0) (z : Hl l (sch.obj X) r 0),
    (∀ j, z.1 j = Ht.cast h (add_zero 0) (cup (l ^ j) (show Ht (l ^ j) (sch.obj X) n 0 from x.1 j)
      (show Ht (l ^ j) (sch.obj X) m 0 from y.1 j))) →
    c (1 ⊗ₜ x) (1 ⊗ₜ y) = 1 ⊗ₜ z

def cupV (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : V l X n →ₗ[ℚ_[l]] V l X m →ₗ[ℚ_[l]] V l X r := pick (IsCup l X h)

def oneV (X : Scheme.{0}) : V l X 0 :=
  pick fun c => ∀ z : Hl l (sch.obj X) 0 0, (∀ j, z.1 j = one (l ^ j) (sch.obj X)) → c = 1 ⊗ₜ z

def IsPush {Y X : Scheme.{0}} (a : Y ⟶ X) (n : ℤ) (T : V l Y n →ₗ[ℚ_[l]] V l X n) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) (hs : ∀ j, s j ≫ a = x),
    IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x) →
    ∀ z, pb l x n (T z) = ∑ j, pb l (s j) n z

def push {Y X : Scheme.{0}} (a : Y ⟶ X) (n : ℤ) : V l Y n →ₗ[ℚ_[l]] V l X n := pick (IsPush l a n)

variable {k : Type} [Field k]

def Pt {X : Scheme.{0}} (p : X ⟶ S k) : Type := {y : S k ⟶ X // y ≫ p = 𝟙 _}

def Pt.map {Y X : Scheme.{0}} {q : Y ⟶ S k} {p : X ⟶ S k} (a : Y ⟶ X) (ha : a ≫ p = q) (y : Pt q) : Pt p :=
  ⟨y.1 ≫ a, by rw [Category.assoc, ha, y.2]⟩

variable (k) in

abbrev PN (N : ℕ) : Scheme.{0} := Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)

variable (k) in

def PNto (N : ℕ) : PN k N ⟶ S k :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))

def IsProj {X : Scheme.{0}} (p : X ⟶ S k) : Prop := ∃ (N : ℕ) (ι : X ⟶ PN k N), IsClosedImmersion ι ∧ ι ≫ PNto k N = p

def SP (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) : Prop := IsProper p ∧ SmoothOfRelativeDimension d p

variable (k) in

abbrev Fam : Type 1 := ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), V l (pullback p p) (2 * d)

variable {l}

def Fam.corr (δ : Fam l k) (d : ℕ) {Y X : Scheme.{0}} {q : Y ⟶ S k} {p : X ⟶ S k} (c a : Y ⟶ X) (hc : c ≫ p = q)
    (ha : a ≫ p = q) : V l Y (2 * d) := pb l (pullback.lift c a (hc.trans ha.symm)) _ (δ d p)

def Fam.cl (δ : Fam l k) (d : ℕ) {X : Scheme.{0}} {p : X ⟶ S k} (y : Pt p) : V l X (2 * d) :=
  δ.corr d (q := p) (𝟙 X) (p ≫ y.1) (Category.id_comp _) (by rw [Category.assoc, y.2, Category.comp_id])

structure IsDiag (δ : Fam l k) : Prop where
  swap : ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ (m : ℤ) (β : V l X m),
    cupV l _ rfl (δ d p) (pb l (pullback.fst p p) m β) = cupV l _ rfl (δ d p) (pb l (pullback.snd p p) m β)
  trans : ∀ (d : ℕ) {Y X : Scheme.{0}} (q : Y ⟶ S k) (p : X ⟶ S k), SP d q → SP d p → ∀ (c a : Y ⟶ X) (hc : c ≫ p = q)
    (ha : a ≫ p = q), Etale (equalizer.ι c a ≫ q) → ∀ s : Finset (Pt q), (∀ y, y ∈ s ↔ y.1 ≫ c = y.1 ≫ a) →
    δ.corr d c a hc ha = ∑ y ∈ s, δ.cl d y
  span : ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ (y : Pt p) (U : X.Opens), (U : Set X) = (Set.range y.1)ᶜ →
    ∀ z : V l X (2 * d), pb l U.ι _ z = 0 → ∃ r : ℚ_[l], z = r • δ.cl d y

variable (l) in

def kun {X Y : Scheme.{0}} (p : X ⟶ S k) (q : Y ⟶ S k) (n : ℤ) :
    (⨁ i : ℤ, V l X i ⊗[ℚ_[l]] V l Y (n - i)) →ₗ[ℚ_[l]] V l (pullback p q) n :=
  DirectSum.toModule _ _ _ fun i => TensorProduct.lift
    ((cupV l (pullback p q) (by omega : i + (n - i) = n)).compl₁₂ (pb l (pullback.fst p q) i) (pb l (pullback.snd p q) (n - i)))

end Defs

def LCover : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p →
  IsIntegral X → ∃ (π : X ⟶ PN k d) (t : Pt (PNto k d)), π ≫ PNto k d = p ∧ IsFinite π ∧ Surjective π ∧
    Etale (equalizer.ι π (p ≫ t.1) ≫ p)

end LateralTheory.EtaleTrace

end
