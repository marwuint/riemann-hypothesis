import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.SupStMonoNormSqPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory Module

noncomputable section

namespace MonomialDegree

def blockEquiv (D : ℕ) : Fin (D + 1) ≃ Ix (Fin (D + 1)) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv _ := rfl

def ptEquiv (D : ℕ) : (Fin (D + 1) → ℂ) ≃ᵐ (Ix (Fin (D + 1)) → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (blockEquiv D)

theorem ptEquiv_apply (D : ℕ) (w : Fin (D + 1) → ℂ) (t : Fin (D + 1)) :
    ptEquiv D w (blockEquiv D t) = w t := by
  rfl

variable {Ω : Type} [Field Ω] {D : ℕ}

variable [CharZero Ω]

end MonomialDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
