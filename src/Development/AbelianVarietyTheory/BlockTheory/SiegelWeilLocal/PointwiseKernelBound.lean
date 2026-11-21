import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound

open Formalism.MainNotions.S GlobalTheory.Count

def decHS (q : ℕ) (h t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))))

end GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound
