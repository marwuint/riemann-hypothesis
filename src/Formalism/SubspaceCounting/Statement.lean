import Mathlib

noncomputable section

open scoped BigOperators

namespace Formalism.G0

def AllButLE {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (π : R)
    (M P : Submodule R X) (g E : ℕ) : Prop :=
  ∃ C : Finset X, (↑C : Set X) ⊆ M ∧ C.card ≤ g ∧
    ∀ x ∈ M, π ^ E • x ∈ P ⊔ Submodule.span R (↑C : Set X)

inductive Slot
  | base
  | ball
  | dual
  deriving DecidableEq

def vertexLabel {V : ℕ} (B : Finset (Fin V)) : Fin V → Slot :=
  fun v => if v ∈ B then Slot.dual else Slot.base

def monoOp {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (e : Fin V → Bool) :
    Module.End R X :=
  ((List.finRange V).map fun v => if e v then y v ^ m else (π ^ S v) • (1 : Module.End R X)).prod

def prodIdealMap {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (M : Submodule R X) :
    Submodule R X :=
  ⨆ e : Fin V → Bool, M.map (monoOp π y m S e)

def WalkSharp : Prop :=
  ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (V : ℕ) (π : R)
    (L : (Fin V → Slot) → Submodule R X) (y : Fin V → Module.End R X)
    (m β c₀ S : ℕ) (a b c Sv : Fin V → ℕ) (g : Finset (Fin V) → ℕ)
    (G : Finset (Fin V) → Finset X),
    1 ≤ m →
    (∀ v w, Commute (y v) (y w)) →
    (∀ σ v, L (Function.update σ v Slot.base) ≤ L (Function.update σ v Slot.ball)) →
    (∀ σ v, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ a v • x ∈ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.base),
      π ^ b v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ c v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      y v x ∈ L (Function.update σ v Slot.dual)) →
    (∀ B : Finset (Fin V), B.card = β + 1 →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ (G B).card ≤ g B ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X)) →
    (∀ v, Sv v ≤ S) →
    AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base))
        (∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1), m ^ (β + 1) * g B)
        (∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S) ∧
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
        (∑ v, Sv v)

end Formalism.G0
