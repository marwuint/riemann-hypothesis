import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

def AffPts (k J : Type) : Type := J → k

instance instTopAffPts (k J : Type) [Field k] : TopologicalSpace (AffPts k J) :=
  .generateFrom {s | ∃ p : MvPolynomial J k, s = {x | MvPolynomial.eval x p ≠ 0}}

instance (k J : Type) [Field k] : Zero (AffPts k J) := ⟨fun _ => 0⟩

variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def CellIdx : Type := Σ i : ι, {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1}

instance [Fintype ι] : Fintype (CellIdx k V) := by
  unfold CellIdx
  infer_instance

variable {k V}

end GlobalTheory.FlagPts
