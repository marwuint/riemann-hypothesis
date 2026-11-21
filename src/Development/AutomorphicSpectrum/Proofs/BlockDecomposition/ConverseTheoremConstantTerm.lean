import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ConverseGL3

local notation "A" => algebraMap ℚ 𝔸[ℚ]

local instance countable_GL2 : Countable (GL (Fin 2) ℚ) :=
  Function.Injective.countable (f := fun (γ : GL (Fin 2) ℚ) (i j : Fin 2) => γ.val i j)
    fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)

end GlobalTheory.CompanionTheory.ConverseGL3
