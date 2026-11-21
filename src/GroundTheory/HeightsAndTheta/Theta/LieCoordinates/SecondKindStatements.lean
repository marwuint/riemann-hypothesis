import Mathlib
import GroundTheory.AutomorphicForms.RealGroupsLie
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace SecondKind

abbrev MatProd {f : ℕ} (p q : Fin f → ℕ) : Type :=
  (τ : Fin f) → Matrix (Fin (p τ) ⊕ Fin (q τ)) (Fin (p τ) ⊕ Fin (q τ)) ℂ

def lieProd {f : ℕ} (p q : Fin f → ℕ) : Submodule ℝ (MatProd p q) :=
  Submodule.pi Set.univ fun τ => indefiniteUnitaryLieAlgebra (p τ) (q τ)

def hsInner {f : ℕ} {p q : Fin f → ℕ} (X X' : MatProd p q) : ℝ :=
  ∑ τ, (trace (X τ * (X' τ)ᴴ)).re

structure OrthoFrame where

  f : ℕ

  r : ℕ
  f_pos : 1 ≤ f
  r_pos : 1 ≤ r

  p : Fin f → ℕ

  q : Fin f → ℕ
  sig : ∀ τ, p τ + q τ = r

  place : Fin (f * r ^ 2) → Fin f

  E : Fin (f * r ^ 2) → MatProd p q
  span : Submodule.span ℝ (Set.range E) = lieProd p q
  orthonormal : ∀ k l, hsInner (E k) (E l) = if k = l then 1 else 0
  supp : ∀ l τ, τ ≠ place l → E l τ = 0

namespace OrthoFrame

end OrthoFrame

def m2 (a b c d : ℂ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.of fun i j => match i, j with
    | .inl _, .inl _ => a
    | .inl _, .inr _ => b
    | .inr _, .inl _ => c
    | .inr _, .inr _ => d

@[simp] theorem block_entry_inl_inl (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inl i) (.inl j) = a := rfl
@[simp] theorem block_entry_inl_inr (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inl i) (.inr j) = b := rfl
@[simp] theorem block_entry_inr_inl (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inr i) (.inl j) = c := rfl
@[simp] theorem block_entry_inr_inr (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inr i) (.inr j) = d := rfl

end SecondKind

end

end GroundTheory.Heights₂.Theta
