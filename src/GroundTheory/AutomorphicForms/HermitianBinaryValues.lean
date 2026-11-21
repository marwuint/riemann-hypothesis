import Mathlib
import GroundTheory.AutomorphicForms.HermitianLocalSplit
import GroundTheory.GlobalFields.Adele.WeakApprox
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
import GroundTheory.GlobalFields.LocalFieldAtPlace

noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global Filter

section Archimedean

open NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {v : InfinitePlace K}

theorem continuous_ringEquivRealOfIsReal (hv : v.IsReal) :
    Continuous (ringEquivRealOfIsReal hv) := by
  have : (ringEquivRealOfIsReal hv : v.Completion → ℝ) = extensionEmbeddingOfIsReal hv := by
    ext x
    simp
  rw [this]
  exact (isometry_extensionEmbeddingOfIsReal hv).continuous

end Archimedean

end GroundTheory.Automorphic
