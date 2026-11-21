import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.DivisionPairOfAdelicFormsFaceColumnsData
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.ReindexBasis

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace Unfolding

section IndefiniteRowSideFullHecke

attribute [local instance] archMulAction

variable {F : Type*} {E : Type} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E] [IsCMField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {N : ℕ}
variable (h : HermitianForm F E W) (v : Basis (Fin N) E W)

def vecStabEquiv (L : Submodule (𝓞 E) (Fin N → E)) (x₀ : W) :
    vecStabGroup h v (latOf v L) x₀ ≃*
      IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x₀) :=
  ((realEquiv h v).subgroupMap _).trans (MulEquiv.subgroupCongr (vecStabGroup.equiv L x₀))

theorem vecStabEquiv_coe (L : Submodule (𝓞 E) (Fin N → E)) (x₀ : W)
    (γ : vecStabGroup h v (latOf v L) x₀) :
    ((vecStabEquiv h v L x₀ γ : IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x₀)) :
      IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)) = realEquiv h v γ := rfl

end IndefiniteRowSideFullHecke

universe u w x

end Unfolding

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison
