import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA.unipotentTranslateContinuity

local notation "𝔞" => algebraMap ℚ 𝔸[ℚ]

instance countable_GL2 : Countable (GL (Fin 2) ℚ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  exact Function.Injective.countable (f := fun g : GL (Fin 2) ℚ => (g : Matrix (Fin 2) (Fin 2) ℚ))
    fun a b h => Units.ext h

instance countable_NQ : Countable NQ := Quotient.countable

theorem val_uni (x y z : 𝔸[ℚ]) :
    ((uni x y z : G3) : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) = !![1, x, y; 0, 1, z; 0, 0, 1] := rfl

end Ad3.GA.unipotentTranslateContinuity
