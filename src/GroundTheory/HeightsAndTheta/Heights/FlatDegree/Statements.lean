import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FlatTheorem

open Matrix NumberField

section Period

variable {n : ℕ}

def hermForm (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  star x ⬝ᵥ (H *ᵥ y)

structure PeriodPoint (p q : ℕ) (H : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) where

  plus : Submodule ℂ (Fin (p + q) → ℂ)

  minus : Submodule ℂ (Fin (p + q) → ℂ)
  isCompl : IsCompl plus minus
  orth : ∀ x ∈ plus, ∀ y ∈ minus, hermForm H x y = 0
  finrank_plus : Module.finrank ℂ plus = p
  finrank_minus : Module.finrank ℂ minus = q
  pos : ∀ x ∈ plus, x ≠ 0 → 0 < (hermForm H x x).re
  neg : ∀ x ∈ minus, x ≠ 0 → (hermForm H x x).re < 0

variable {p q : ℕ} {H : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}

def PeriodPoint.proj (y : PeriodPoint p q H) (x : Fin (p + q) → ℂ) : Fin (p + q) → ℂ :=
  (Submodule.projectionOnto y.plus y.minus y.isCompl x : Fin (p + q) → ℂ)

end Period

end GroundTheory.Heights₂.Heights.FlatTheorem
