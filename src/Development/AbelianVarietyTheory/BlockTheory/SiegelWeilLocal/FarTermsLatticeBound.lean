import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound

open Formalism.MainNotions.S GlobalTheory.Count

def farSet (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d ep x γ}

def latFactor (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / tau1 I x ^ 2) ^ (2 * (I.n ^ 2 * I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound
