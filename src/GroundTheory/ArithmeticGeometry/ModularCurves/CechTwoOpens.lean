import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor

open CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

section TwoOpens

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : Fin 2 → Opens X)

abbrev i01 : Fin 2 → Fin 2 := ![0, 1]

noncomputable def twoDiff : Cochain P U 0 →+ P.obj (op (inter U i01)) :=
  (Pi.evalAddMonoidHom (fun i => P.obj (op (inter U i))) i01).comp (d P U 0)

abbrev TwoQuot : Type u := P.obj (op (inter U i01)) ⧸ (twoDiff P U).range

noncomputable def cocycleToQuot : cocycles P U 1 →+ TwoQuot P U :=
  (QuotientAddGroup.mk' _).comp
    ((Pi.evalAddMonoidHom (fun i => P.obj (op (inter U i))) i01).comp (cocycles P U 1).subtype)

lemma cocycleToQuot_apply (σ : cocycles P U 1) :
    cocycleToQuot P U σ = QuotientAddGroup.mk ((σ : Cochain P U 1) i01) := rfl

noncomputable def cechOneToQuot : cechH P U 1 →+ TwoQuot P U :=
  QuotientAddGroup.lift _ (cocycleToQuot P U) (by
    rintro ⟨σ, hσ⟩ hb
    rw [AddSubgroup.mem_addSubgroupOf, coboundaries_succ] at hb
    obtain ⟨τ, rfl⟩ := hb
    rw [AddMonoidHom.mem_ker, cocycleToQuot_apply, QuotientAddGroup.eq_zero_iff]
    exact ⟨τ, rfl⟩)

lemma cechOneToQuot_cls (σ : Cochain P U 1) (hσ : d P U 1 σ = 0) :
    cechOneToQuot P U (cls σ hσ) = QuotientAddGroup.mk (σ i01) := rfl

end TwoOpens

end GroundTheory.Arith.Modular
