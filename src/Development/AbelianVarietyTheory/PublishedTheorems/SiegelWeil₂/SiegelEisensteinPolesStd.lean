import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger

noncomputable section

open scoped Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7} {n : ℕ}

def IsSection (χ : (AE D)ˣ →* Circle) (s : ℂ) (φ : G D n → ℂ) : Prop :=
  (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
    φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (s + (n : ℂ) / 2) * φ g) ∧
  Continuous φ ∧ IsKFinite (K D n) φ

def stdSec (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s₁ s : ℂ) : G D n → ℂ := fun g => φ g * npow (H g) (s - s₁)

end GlobalTheory.StdUnn

namespace GlobalTheory.Published

end GlobalTheory.Published

end
