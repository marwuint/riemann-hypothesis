import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace CompanionTheory.jumpWindows

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

def GlobalTheory (m : ℕ) (γ : GL (Fin a) R) : Prop :=
  ∀ i k : Fin a, (m ≤ (i : ℕ) ∨ m ≤ (k : ℕ)) → γ.val i k = (1 : Matrix (Fin a) (Fin a) R) i k

end Ring

end CompanionTheory.jumpWindows

end
