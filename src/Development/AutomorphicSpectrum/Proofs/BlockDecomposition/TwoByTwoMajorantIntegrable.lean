import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Set Filter

namespace GlobalTheory.CompanionTheory.TwoByTwoMajorant

def coord : (Fin 2 → Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → ℝ)).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

theorem coord_apply (h : Fin 2 → Fin 2 → ℝ) :
    coord h = ((h 0 0, h 0 1), (h 1 0, h 1 1)) := rfl

end GlobalTheory.CompanionTheory.TwoByTwoMajorant
