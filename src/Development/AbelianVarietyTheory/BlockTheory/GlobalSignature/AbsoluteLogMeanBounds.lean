import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients Classical

def mean (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (X : (M →ₐ[ℚ] ℂ) → ℝ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, X ρ) / (Module.finrank ℚ M : ℝ)

def IsConjugateCurvePointLift (D : D7) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  ∀ ρ, IsTwoTorsionPointUnkilled D (lamConj M ρ Λ) (t ρ)

def kronBound (D : D7) : ℝ :=
  (1 / 2) * (Real.log (Real.sqrt (D.host.d : ℝ)) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

def HidaSetting (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ DataIn D (tor0 D cc δ) M ∧ IsConjugateCurvePointLift D (lamOf D cc δ) M t

end GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds
