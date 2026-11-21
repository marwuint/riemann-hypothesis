import Formalism.LogVandermondeBounds.FinrankFiberSumZero

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}

def opGs (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, ψ (c : k) * φ ((c : k) • f)

def opGsStar (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, (starRingEnd ℂ) (ψ (c : k)) * φ (((c⁻¹ : kˣ) : k) • f)

def opFF (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (x : Fin r → k) : ℂ :=
  ∑ f ∈ univ.filter (fun f => f ≠ 0), ψ (pair f x) * φ f

end Ops

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
