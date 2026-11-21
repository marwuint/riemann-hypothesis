import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.UpqRep
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Formalism.HermitianCurvature.StatementTBB
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingGapDecay
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CapelliKFiniteCoefficient
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPair
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBessel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCell
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionalsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero

theorem continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞}
    {f : B.Mat k r → E} (h : B.CkOn m (B.GV k r) f) : ContinuousOn f (B.GV k r) := by
  letI : NormedAddCommGroup (B.Mat k r) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (B.Mat k r) := Matrix.normedSpace
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  have h1 : ContinuousWithinAt f' (B.GV k r) g₀ :=
    (hf'.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (he g₀ hgU hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g a b
  exact he g a b

end GlobalTheory.CoefZero
