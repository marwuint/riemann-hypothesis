import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.DivisionPairOfAdelicFormsFaceColumnsData
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
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

end IndefiniteRowSideFullHecke

universe u w x

end Unfolding

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison
