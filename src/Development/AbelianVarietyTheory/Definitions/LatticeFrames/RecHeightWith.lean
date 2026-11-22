import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam

noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

def DelNat (D : D7) : Prop := ∃ n : ℕ, D.s.Del = n

def ThickUp {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → wj D j τ ≤ L.sc.b + L.etaSz + 1

end GlobalTheory.CoreHt
