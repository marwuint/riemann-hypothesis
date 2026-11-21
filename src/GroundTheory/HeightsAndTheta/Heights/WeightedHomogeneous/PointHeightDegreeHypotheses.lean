import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)

noncomputable section

section Metric

open Matrix
open scoped ComplexOrder

variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

theorem oneBlockMetricAgrees_iff (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (F : HermLattice K (r + 1))
    (A : HermLine (oneBlockSizes e r)) :
    OneBlockMetricAgrees om F A ↔
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
        A.metric (fun _ t ↦ σ (om ((oneBlockIndex e r).symm.symm t).1 : K) *
          w ((oneBlockIndex e r).symm.symm t).2) = hermNorm (F.metric σ) w :=
  Iff.rfl

end Metric

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
