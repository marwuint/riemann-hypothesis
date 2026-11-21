import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.FsMetricFinIsSemipositive
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

namespace ProjPotDens

open ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockCLM (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (⟨k, i⟩ : Σ k, ι k)

omit [Fintype K] [∀ k, Fintype (ι k)] in
@[simp] theorem blockCLM_apply (k : K) (z : (Σ k, ι k) → ℂ) (i : ι k) :
    blockCLM k z i = z ⟨k, i⟩ := rfl

end ProjPotDens

end GroundTheory.Heights₂.Heights.Targets
