import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.Tr

def Splits {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) : Prop :=
  ∃ hs : ∀ j, s j ≫ a = x, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x)

section
variable (R : Type) [CommRing R]

abbrev fr (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

abbrev gen {U X : Scheme.{0}} (x : U ⟶ X) : Sec (fr R X) U := freeGen R (yoneda.obj X) U x

def IsTr {Y X : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
    Sec.map τ (gen R x) = ∑ j, gen R (s j)

variable {R}

end

def LSpl : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
  (∀ (U : Scheme.{0}) (w : U ⟶ W), Splits a (w ≫ x) m (fun j => w ≫ s j)) ∧
  (∀ y : W ⟶ Y, y ≫ a = x → ∀ t : W, ∃ (O : W.Opens) (j : Fin m), t ∈ O ∧ O.ι ≫ y = O.ι ≫ s j) ∧
  (Nonempty W → Function.Injective s)

def LLoc : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (W : Scheme.{0}) (x : W ⟶ X) (t : W),
  ∃ (U : Scheme.{0}) (g : U ⟶ W) (m : ℕ) (s : Fin m → (U ⟶ Y)), Etale g ∧ t ∈ Set.range g ∧ Splits a (g ≫ x) m s

def LTau : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ τ : fr R X ⟶ fr R Y, IsTr R a τ

section Glue
variable (l : ℕ) [Fact l.Prime]

def lev (E : Spc) (n : ℤ) (j : ℕ) : Hl l E n 0 →+ Ht (l ^ j) E n 0 where
  toFun z := z.1 j
  map_zero' := rfl
  map_add' _ _ := rfl

end Glue

end LateralTheory.EtaleTrace.Tr

end
