import Mathlib

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace EffectiveHS

open Finset

structure MulTower (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] where

  W : Submodule R A

  V : ℕ → Submodule R A

  mul_mem : ∀ j, ∀ w ∈ W, ∀ f ∈ V j, w * f ∈ V (j + 1)

namespace MulTower

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)

def Raises (k : ℕ) (x : A) : Prop := ∀ j, ∀ f ∈ τ.V j, x * f ∈ τ.V (j + k)

theorem raises_one : τ.Raises 0 1 := by
  intro j f hf
  simpa using hf

theorem Raises.mul {τ : MulTower R A} {k l : ℕ} {x y : A} (hx : τ.Raises k x)
    (hy : τ.Raises l y) : τ.Raises (k + l) (x * y) := by
  intro j f hf
  have e : j + (k + l) = j + l + k := by omega
  rw [e, mul_assoc]
  exact hx _ _ (hy j f hf)

theorem Raises.pow {τ : MulTower R A} {k : ℕ} {x : A} (hx : τ.Raises k x) (n : ℕ) :
    τ.Raises (k * n) (x ^ n) := by
  induction n with
  | zero => simpa using τ.raises_one
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact ih.mul hx

variable {D : ℕ} {s : Fin D → A}

end MulTower

end EffectiveHS

end GroundTheory.Heights₂.Heights
