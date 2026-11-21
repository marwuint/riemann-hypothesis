import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def stdCoordMap (K : Type*) [Field K] (n : ℕ) : (Fin n → 𝓞 K) →ₗ[𝓞 K] (Fin n → K) :=
  LinearMap.pi fun i => (Algebra.linearMap (𝓞 K) K).comp (LinearMap.proj i)

theorem stdCoordMap_apply (K : Type*) [Field K] (n : ℕ) (v : Fin n → 𝓞 K) (i : Fin n) :
    stdCoordMap K n v i = (v i : K) := rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
