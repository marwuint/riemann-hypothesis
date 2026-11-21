import Mathlib
import GroundTheory.TateCohomology.CohTrivialBasic
import GroundTheory.TateCohomology.DimensionShift
import GroundTheory.TateCohomology.TateTransport
import GroundTheory.TateCohomology.ResCoresZero

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

namespace IsTateDelta

end IsTateDelta

section LE

variable {U W : Subgroup G} (h : W ≤ U)

@[simps]
def resLENatTrans :
    resFunctor U.subtype ⋙ resFunctor (W.subgroupOf U).subtype ⋙
        resFunctor ((Subgroup.subgroupOfEquivOfLe h).symm : W →* W.subgroupOf U) ⟶
      resFunctor (k := k) W.subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl

@[simps]
def coresLENatTrans :
    resFunctor W.subtype ⋙ resFunctor (Subgroup.subgroupOfEquivOfLe h : W.subgroupOf U →* W) ⟶
      resFunctor (k := k) U.subtype ⋙ resFunctor (W.subgroupOf U).subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl

variable [Fintype U] [Fintype W]

omit [Fintype U] [Fintype W] in

def invariantsLE {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (res W.subtype A).ρ.invariants :=
  ⟨y, fun w => y.2 ⟨w, h w.2⟩⟩

omit [Fintype U] [Fintype W] in
@[simp]
lemma coe_invariantsLE {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (invariantsLE h y : A) = y := rfl

end LE

end GroundTheory.GroupCoh
