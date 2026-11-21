import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamChartInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegularInjectivePieces.Statement : Prop :=
  ∀ (d : ℕ) (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin d → ℂ), IsOpen U → DifferentiableOn ℂ g U →
    ∃ P : ℕ → Set (Fin d → ℂ), (∀ i, MeasurableSet (P i)) ∧ Pairwise (Function.onFun Disjoint P) ∧
      ⋃ i, P i = {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
      ∀ i, Set.InjOn g (P i)

end

end GroundTheory.Heights₂.Heights
