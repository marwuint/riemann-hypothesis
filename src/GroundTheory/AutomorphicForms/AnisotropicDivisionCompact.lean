import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicRestrict
import GroundTheory.AutomorphicForms.AnisotropicHeight
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable (K : Type*) [Field K] [NumberField K] (D : Type*) [DivisionRing D] [Algebra K D]

abbrev adeleTensorTopology : TopologicalSpace (𝔸[K] ⊗[K] D) :=
  moduleTopology 𝔸[K] (𝔸[K] ⊗[K] D)

attribute [local instance] adeleTensorTopology

theorem isModuleTopology_adeleTensor : IsModuleTopology 𝔸[K] (𝔸[K] ⊗[K] D) := ⟨rfl⟩

attribute [local instance] isModuleTopology_adeleTensor

theorem isTopologicalRing_adeleTensor [FiniteDimensional K D] :
    IsTopologicalRing (𝔸[K] ⊗[K] D) :=
  IsModuleTopology.isTopologicalRing 𝔸[K] _

attribute [local instance] isTopologicalRing_adeleTensor

variable {K D}

variable [FiniteDimensional K D] {d : ℕ} (b : Basis (Fin d) K D)

theorem continuous_coords_adele : Continuous (coords b 𝔸[K]) :=
  IsModuleTopology.continuous_of_linearMap (coords b 𝔸[K]).toLinearMap

theorem continuous_coords_adele_symm : Continuous (coords b 𝔸[K]).symm := by
  have h : ⇑(coords b 𝔸[K]).symm = fun y => ∑ k, y k • baseBasis b 𝔸[K] k := by
    funext y
    exact Module.Basis.equivFun_symm_apply _ y
  rw [h]
  exact continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const

def coordsHomeomorph : 𝔸[K] ⊗[K] D ≃ₜ (Fin d → 𝔸[K]) where
  toEquiv := (coords b 𝔸[K]).toEquiv
  continuous_toFun := continuous_coords_adele b
  continuous_invFun := continuous_coords_adele_symm b

variable (K D) in
theorem t2Space_adeleTensor : T2Space (𝔸[K] ⊗[K] D) :=
  (coordsHomeomorph (Module.finBasis K D)).isEmbedding.t2Space

attribute [local instance] t2Space_adeleTensor

end Anisotropic

end

end GroundTheory.Automorphic
