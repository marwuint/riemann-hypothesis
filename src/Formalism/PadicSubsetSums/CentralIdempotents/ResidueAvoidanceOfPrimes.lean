import Mathlib

noncomputable section

open Classical

namespace Formalism.IrreducibleCountingLemmas.TOP

def sg (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def SgLe : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (H : ℕ), 2 ≤ ℓ → (∀ j, h j ≤ H) →
    ∀ i, (sg f ℓ h i : ℝ) ≤ H / ((ℓ : ℝ) - 1)

def SgRange : Prop :=
  ∀ (ℓ : ℕ) (ℓs b H : ℝ), 0 ≤ H → 1 < ℓs → ℓs < ℓ → H * ℓs ≤ 2 * b * (ℓs - 1) →
    H / ((ℓ : ℝ) - 1) ≤ 2 * b / ℓs

end Formalism.IrreducibleCountingLemmas.TOP
