import Mathlib
import GroundTheory.LocalFields.TameExtension
import GroundTheory.ProfiniteCohomology.IsProPGroupSubgroupIffIsPGroupMap
import GroundTheory.ProfiniteCohomology.NotDvdSuperIndexIffMap
import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField
set_option maxSynthPendingDepth 1

noncomputable section

open IntermediateField ValuativeRel InfiniteGalois GroundTheory.ProfCoh

namespace GroundTheory.LocalField

section Definition

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω]

def inertiaGroup : Subgroup (Ω ≃ₐ[K] Ω) := (maximalUnramifiedExtension K Ω).fixingSubgroup

def wildInertiaGroup : Subgroup (Ω ≃ₐ[K] Ω) := (tameExtension K Ω).fixingSubgroup

end Definition

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

instance normal_inertiaGroup : (inertiaGroup K Ω).Normal :=
  IsGalois.fixingSubgroup_normal_of_isGalois _

instance normal_wildInertiaGroup : (wildInertiaGroup K Ω).Normal :=
  IsGalois.fixingSubgroup_normal_of_isGalois _

end SeparableClosure

end GroundTheory.LocalField
