import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SymmetricPatternGroup

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sE {n m : Type*} (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)

end Plain

end GlobalTheory.SymCompare
