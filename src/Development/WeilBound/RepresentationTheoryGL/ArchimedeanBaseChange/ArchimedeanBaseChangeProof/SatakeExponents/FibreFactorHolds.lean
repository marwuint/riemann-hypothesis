import Mathlib

noncomputable section

open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def ExpSum : Prop := ∀ (ι : Type) [Fintype ι] (c lam : ι → ℂ) (ρ C : ℝ) (N : ℕ), 0 ≤ ρ →
  (∀ᶠ k : ℕ in Filter.atTop, ‖∑ i, c i * lam i ^ k‖ ≤ C * (1 + k) ^ N * ρ ^ k) →
  ∀ μ : ℂ, ρ < ‖μ‖ → ∑ i with lam i = μ, c i = 0

def fibre {A : Type} [CommRing A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] {ι : Type} (As : ι → Type)
    [∀ s, CommRing (As s)] [∀ s, Algebra ℂ (As s)] [∀ s, StarRing (As s)] [∀ s, StarModule ℂ (As s)]
    (ev : ∀ s, As s →⋆ₐ[ℂ] A) : StarSubalgebra ℂ (A × ∀ s, As s) where
  carrier := {x | ∀ s, ev s (x.2 s) = x.1}
  mul_mem' := fun {x y} hx hy s => by simp [hx s, hy s]
  add_mem' := fun {x y} hx hy s => by simp [hx s, hy s]
  algebraMap_mem' := fun z s => by simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := fun {x} hx s => by simp [map_star, hx s]

end PositivityTheory.Rg.BcB.F

end
