import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def Cut (j d : ℕ) (c a : Fin d) : Prop := (a : ℕ) < j ∧ j ≤ (c : ℕ) ∧ ((a : ℕ) = 0 ∨ (c : ℕ) + 1 = d)

instance (j d : ℕ) (c a : Fin d) : Decidable (Cut j d c a) := by unfold Cut; infer_instance

variable (k V) in

def LocIdx (j : ℕ) : Type :=
  Σ i, {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1 ∧ ¬ Cut j _ p.1 p.2}

instance [Fintype ι] (j : ℕ) : Fintype (LocIdx k V j) := by
  unfold LocIdx
  infer_instance

end GlobalTheory.FlagPts
