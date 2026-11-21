import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TorusWeightEigenAndRootShift
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.UpqRep
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.torusWeight_eigen_and_rootShift : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ (ν : Fin (2 * r + k + 1) → ℝ) (v : R.smSub), PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) ν (v : R.H) → Formalism.REAL.IsWeight E ν v ∧ ∀ a b, PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (ν + PI.UpqRep.root a b) ((E a b v : R.smSub) : R.H) := by
  exact @GlobalTheory.TorusWeight.torus_weight_action
