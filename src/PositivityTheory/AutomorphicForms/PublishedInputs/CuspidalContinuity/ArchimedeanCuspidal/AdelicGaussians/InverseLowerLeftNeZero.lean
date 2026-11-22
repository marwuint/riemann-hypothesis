import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.HeisenbergLowerCommuteMiddle

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA.CtvP

open Ad3.GA.unipotentTranslateContinuity

local notation "𝔞" => algebraMap ℚ 𝔸[ℚ]

def chiH (ξ : Fin 2 → ℚ) (y : Fin 3 → 𝔸[ℚ]) : ℂ :=
  (adelicChar ℚ (-(𝔞 (ξ 0) * y 0 + 𝔞 (ξ 1) * y 1)) : ℂ)

section reps

variable {ξ : Fin 2 → ℚ} (hξ0 : ξ 0 ≠ 0) (hξ1 : ξ 1 ≠ 0)

def gU : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, ξ 0 * ξ 1; ξ 1, 0] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])

def gV : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ξ 0)⁻¹, 0; 0, (ξ 0 * ξ 1)⁻¹] (by
    simp [Matrix.det_fin_two_of, hξ0, hξ1])

end reps

end Ad3.GA.CtvP

namespace Ad3.GA

end Ad3.GA
