import Mathlib
import Formalism.DistinguishedUnitIdeals.Statement

noncomputable section

namespace Formalism.ExponentWindows

def NbThin {K D : Type} [Field K] [AddCommGroup D] [Module K D] (k : ℤ) : Submodule K D :=
  if k < 0 then ⊥ else ⊤

def NbUp {K D : Type} [Field K] [AddCommGroup D] [Module K D] (b : ℤ) (C : Submodule K D)
    (k : ℤ) : Submodule K D :=
  if k < -b then ⊥ else if k < 0 then C else ⊤

def NbDown {K D : Type} [Field K] [AddCommGroup D] [Module K D] (b : ℤ) (F : Submodule K D)
    (k : ℤ) : Submodule K D :=
  if k < 0 then ⊥ else if k < b then F else ⊤

def IsFilt {K D : Type} [Field K] [AddCommGroup D] [Module K D] (Fil : ℤ → Submodule K D) : Prop :=
  Antitone Fil ∧ (∃ lo : ℤ, Fil lo = ⊤) ∧ (∃ hi : ℤ, Fil hi = ⊥)

def Rounding : Prop :=
  ∀ (K D : Type) [Field K] [AddCommGroup D] [Module K D] (Fil : ℤ → Submodule K D)
    (G S η g b : ℤ), IsFilt Fil → 0 ≤ G → 0 ≤ S → 0 ≤ η → G ≤ g → S ≤ g → η ≤ g → g < b →
    ((∀ u, Fil u ≠ Fil (u + 1) → -G ≤ u ∧ u ≤ G) →
      ∀ i, NbThin (i - g) ≤ Fil (-i) ∧ Fil (-i) ≤ NbThin (i + g)) ∧
    ((∀ u, Fil u ≠ Fil (u + 1) → (b ≤ u ∧ u ≤ b + S) ∨ (-η ≤ u ∧ u ≤ η)) →
      ∀ i, NbUp b (Fil b) (i - g) ≤ Fil (-i) ∧ Fil (-i) ≤ NbUp b (Fil b) (i + g)) ∧
    ((∀ u, Fil u ≠ Fil (u + 1) → (-b - S ≤ u ∧ u ≤ -b) ∨ (-η ≤ u ∧ u ≤ η)) →
      ∀ i, NbDown b (Fil (-η)) (i - g) ≤ Fil (-i) ∧ Fil (-i) ≤ NbDown b (Fil (-η)) (i + g))

end Formalism.ExponentWindows
