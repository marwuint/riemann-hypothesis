import Mathlib
import GroundTheory.GlobalFields.Artin.Places
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

section Finite

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))

omit [NumberField K] [NumberField L] [IsGalois K L] in

instance normal_inertia_subgroupOf_stabilizer :
    ((w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)).Normal :=
  ⟨fun n hn g ↦ by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact mul_mul_inv_mem_inertia g.2 hn⟩

end Finite

end GroundTheory.Global.Artin
