import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ExistsTowerOfLocalSetting
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mat_mul_mem_UH_Hpk {k r : ℕ} {g h : CayleySignature.Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hh : h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : g * h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = Formalism.QuantumDeterminants.Hpk k r
  calc (g * h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hg', hh']

end Formalism.MainNotions.LeviCoordinates

end
