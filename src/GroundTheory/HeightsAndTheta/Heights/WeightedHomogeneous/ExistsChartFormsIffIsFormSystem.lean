import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

namespace AddBlockData

def toObjects (D : AddBlockData P) : Heights.AddBlockData P where
  deg := D.deg
  size := D.m
  elt j := (funFieldEquiv P).symm (D.x j)
  elt_deg j := (isOfDegree_iff P D.deg _).2 (by rw [RingEquiv.apply_symm_apply]; exact D.homog j)
  chart_mem c hc j := by
    rw [← funFieldEquiv_mem_chartRing_iff, funFieldEquiv_div_chartPow, RingEquiv.apply_symm_apply]
    exact D.chart c hc j
  generating c hc := by
    obtain ⟨u, hu, hsum⟩ := D.unit c hc
    refine ⟨fun j ↦ (funFieldEquiv P).symm (u j), fun j ↦ ?_, ?_⟩
    · rw [← funFieldEquiv_mem_chartRing_iff, RingEquiv.apply_symm_apply]
      exact hu j
    · apply (funFieldEquiv P).injective
      simp only [map_sum, map_mul, funFieldEquiv_div_chartPow, RingEquiv.apply_symm_apply, map_one]
      exact hsum

end AddBlockData

open _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

namespace ChartForms

variable {D : AddBlockData P}

end ChartForms

section Metric

variable {D : AddBlockData P}

theorem den_eq (G : ChartForms D) (Γ : GenSystem P) :
    den G Γ = (toObjects D).den G.d G.g Γ.f Γ.δ := rfl

end Metric

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
