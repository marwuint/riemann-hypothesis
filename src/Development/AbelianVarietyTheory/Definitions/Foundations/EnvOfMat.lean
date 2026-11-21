import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SOrb

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def opn {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))‖

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end GlobalTheory.SOrb
