import Mathlib

open Filter Topology
open scoped ContDiff

noncomputable section

namespace SmoothVectors

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsClosedMatrixGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G ∧ (∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) ∧
    ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1

def lieAlg (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G}

end SmoothVectors

end
