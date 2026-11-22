import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

section Zero
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]

def ordZ (hc : 0 + c = c) : Fin κ ⊕ Fin c ≃ XIx (Fin κ) t 0 ⊕ Fin c :=
  (ixZero (Fin κ ⊕ Fin c) t).trans (stdOrd (Fin κ) t 0 c hc)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Zero

end GlobalTheory.SymDec

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
