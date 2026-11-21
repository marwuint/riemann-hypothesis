import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.GL2Classical.ExistsIntOfMemIntegralFiniteAdeles
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import Mathlib
import GroundTheory.AutomorphicForms.ReductionSiegel

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing

namespace Ad3.GA

local notation "M3A" => Matrix (Fin 3) (Fin 3) 𝔸[ℚ]

namespace majorantEstimates

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (γ : GL (Fin 2) ℚ) :
    ((e1 γ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![(γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1, 0;
        (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1, 0; 0, 0, 1] := rfl

end majorantEstimates

end Ad3.GA
