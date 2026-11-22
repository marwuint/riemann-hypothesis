import Mathlib
import GroundTheory.AutomorphicForms.RealGroupsLie
set_option maxSynthPendingDepth 1

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set

set_option linter.unusedSectionVars false

noncomputable section

def RegNorm (𝔅 : Type*) : Type _ := 𝔅

namespace RegNorm

variable (𝔅 : Type*) [Ring 𝔅] [Algebra ℝ 𝔅] [FiniteDimensional ℝ 𝔅]

instance : Ring (RegNorm 𝔅) := inferInstanceAs (Ring 𝔅)

instance : Algebra ℝ (RegNorm 𝔅) := inferInstanceAs (Algebra ℝ 𝔅)

instance : FiniteDimensional ℝ (RegNorm 𝔅) := inferInstanceAs (FiniteDimensional ℝ 𝔅)

def toRegNorm : 𝔅 ≃ₐ[ℝ] RegNorm 𝔅 := AlgEquiv.refl

open scoped Matrix.Norms.L2Operator

def leftReg : RegNorm 𝔅 →ₐ[ℝ] Matrix (Fin (Module.finrank ℝ 𝔅)) (Fin (Module.finrank ℝ 𝔅)) ℝ :=
  Algebra.leftMulMatrix (Module.finBasis ℝ 𝔅)

theorem leftReg_injective : Function.Injective (leftReg 𝔅) :=
  Algebra.leftMulMatrix_injective _

instance : NormedRing (RegNorm 𝔅) :=
  NormedRing.induced (RegNorm 𝔅) _ (leftReg 𝔅) (leftReg_injective 𝔅)

instance : NormedAlgebra ℝ (RegNorm 𝔅) :=
  NormedAlgebra.induced ℝ (RegNorm 𝔅) _ (leftReg 𝔅)

instance : CompleteSpace (RegNorm 𝔅) := FiniteDimensional.complete ℝ _

variable [TopologicalSpace 𝔅] [IsTopologicalAddGroup 𝔅] [ContinuousSMul ℝ 𝔅]

end RegNorm

section FormGroup

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [FiniteDimensional ℝ 𝔄]
  (σ : 𝔄 →ₗ[ℝ] 𝔄) (hσ1 : σ 1 = 1) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (J : 𝔄ˣ)

end FormGroup

end

end GroundTheory.Automorphic
