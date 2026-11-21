import Mathlib

noncomputable section

namespace SiegelEisensteinSeries

open Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def WHolo (D : Set (E →ₗ[ℂ] ℂ)) (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ ν ∈ D, DifferentiableOn ℂ (fun s => ν (f s)) U

structure LinSys (E : Type*) [AddCommGroup E] [Module ℂ E] (I : Type*) where
  a : I → ℂ → E →ₗ[ℂ] ℂ
  c : I → ℂ → ℂ

variable {I : Type*}

end SiegelEisensteinSeries
