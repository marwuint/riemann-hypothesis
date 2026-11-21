import Mathlib

set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.Shintani

def openCone {W : Type} [AddCommGroup W] [Module ℚ W] (s : Finset W) : Set W :=
  {x | ∃ t : W → ℚ, (∀ v ∈ s, 0 < t v) ∧ x = ∑ v ∈ s, t v • v}

def IsSimplicial {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) (s : Finset W) : Prop :=
  s.Nonempty ∧ LinearIndepOn ℚ id (s : Set W) ∧ (s : Set W) ⊆ P

def coneFuns {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) : Submodule ℚ (W → ℚ) :=
  Submodule.span ℚ {f | ∃ s : Finset W, IsSimplicial P s ∧ f = (openCone s).indicator 1}

def IsPosCone {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) : Prop :=
  ∀ u ∈ P, ∀ v ∈ P, ∀ a b : ℚ, 0 < a → 0 < b → a • u + b • v ∈ P

def totPos (F : Type) [Field F] : Set F := {x | ∀ σ : F →+* ℝ, 0 < σ x}

def IsEntRat {ι : Type} (f N : ι → ℚ) : Prop :=
  ∃ A : ℂ → ℂ, Differentiable ℂ A ∧ (∀ s : ℂ, 1 < s.re → HasSum (fun i => (f i : ℂ) * (N i : ℂ) ^ (-s)) (A s)) ∧
    ∀ k : ℕ, ∃ r : ℚ, A (-(k : ℂ)) = (r : ℂ)

def IsBalanced {ι : Type} [DecidableEq ι] (l : ℕ) (φ : (ι → ℕ) → ℚ) : Prop :=
  (∀ i j, φ (Function.update j i (j i + l)) = φ j) ∧ ∀ i j, ∑ t ∈ Finset.range l, φ (Function.update j i t) = 0

end GlobalTheory.Shintani
