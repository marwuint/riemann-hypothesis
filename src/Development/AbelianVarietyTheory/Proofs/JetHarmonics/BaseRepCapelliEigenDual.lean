import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatrixCoefficientSmoothDerivatives
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneous
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaInfEqIntegralOfIntegrableCoefficient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqConstMulArchPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBessel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCell
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal Matrix.Norms.Elementwise in

theorem _root_.GlobalTheory.CoefZero.continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {m : ℕ∞}
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (h : _root_.Formalism.FourierDecayAlt.B.CkOn m (_root_.Formalism.FourierDecayAlt.B.GV k r) f) : ContinuousOn f (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfeq⟩ := h g₀ hg₀
  have hc : ContinuousOn f' U := hf'.continuousOn
  have hcont : ContinuousAt f' g₀ := hc.continuousAt (hU.mem_nhds hgU)
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (hfeq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (_root_.Formalism.FourierDecayAlt.B.GV k r) (hU.mem_nhds hgU)] with g hg
  exact hfeq g hg.2 hg.1

end GlobalTheory.CoefZero
