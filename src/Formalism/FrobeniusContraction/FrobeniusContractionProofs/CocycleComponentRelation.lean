import Formalism.FrobeniusContraction.Statement

namespace Formalism.WachCohomologyFacts.PExt

open Formalism.WachCohomologyFacts

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA]
variable {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V]

def extMap (f : V →ₗ[O] V) (g : AA →ₐ[O] AA) (w : V) : V × AA →ₗ[O] V × AA where
  toFun p := (f p.1 + g p.2 • w, g p.2)
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk, Prod.mk.injEq,
      and_true]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk, smul_add,
      smul_assoc]

@[simp] lemma extMap_apply (f : V →ₗ[O] V) (g : AA →ₐ[O] AA) (w : V) (p : V × AA) :
    extMap f g w p = (f p.1 + g p.2 • w, g p.2) := rfl

end Formalism.WachCohomologyFacts.PExt
