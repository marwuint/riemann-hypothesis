import Mathlib
import GroundTheory.Brauer.AbsoluteGalois
import GroundTheory.Brauer.BaseChangeCentralizer
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

section Topology

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

def galUnitsRestrictScalars (E : IntermediateField K Ks) :
    Rep.res (AlgEquiv.restrictScalarsHom K : (Ks ≃ₐ[E] Ks) →* (Ks ≃ₐ[K] Ks)) (galUnits.{u} K Ks) ⟶
      galUnits.{u} E Ks :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ksˣ) (B := Additive Ksˣ) (AddMonoidHom.id _),
    fun σ => by
      ext x
      rfl⟩

@[simp]
theorem galUnitsRestrictScalars_hom_apply (E : IntermediateField K Ks) (x : Additive Ksˣ) :
    (galUnitsRestrictScalars E).hom x = x :=
  rfl

end Topology

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

instance isSepClosure_intermediateField (E : IntermediateField K Ks) : IsSepClosure E Ks :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ks⟩

variable (E : IntermediateField K Ks)

instance isDiscreteRep_res_fixingSubgroup :
    IsDiscreteRep (Rep.res E.fixingSubgroup.subtype (galUnits.{u} K Ks)) :=
  isDiscreteRep_res_subtype _ _

end Main

end GroundTheory.Brauer
