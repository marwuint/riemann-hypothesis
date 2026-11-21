import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCohomology

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe w' u

namespace GroundTheory.Arith.SchemeCoh

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

section Repartitions

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

variable (k X) in

def repartitions : Submodule k (PrimeDivisor X → X.functionField) where
  carrier := {a | {Z : PrimeDivisor X | ¬ Z.valuation (a Z) ≤ 1}.Finite}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    refine (ha.union hb).subset fun Z hZ => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hZ ((Valuation.map_add _ _ _).trans (max_le hc.1 hc.2))
  smul_mem' c {a} ha := by
    refine ha.subset fun Z hZ => ?_
    intro h
    apply hZ
    change Z.valuation (c • a Z) ≤ 1
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * 1 := mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) h
      _ = 1 := one_mul 1

variable (k) in

def boundedRepartitions (D : WeilDivisor X) : Submodule k (repartitions k X) where
  carrier := {a | ∀ Z : PrimeDivisor X, a.1 Z ∈ Z.divisorSubgroup D}
  zero_mem' Z := (Z.divisorSubgroup D).zero_mem
  add_mem' {a b} ha hb Z := (Z.divisorSubgroup D).add_mem (ha Z) (hb Z)
  smul_mem' c {a} ha Z := by
    have h := ha Z
    rw [PrimeDivisor.mem_divisorSubgroup] at h ⊢
    change Z.valuation (c • a.1 Z) ≤ _
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * WithZero.exp (D Z) := mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) h
      _ = _ := one_mul _

lemma mem_boundedRepartitions (D : WeilDivisor X) (a : repartitions k X) :
    a ∈ boundedRepartitions k D ↔ ∀ Z : PrimeDivisor X, a.1 Z ∈ Z.divisorSubgroup D := Iff.rfl

end Repartitions

section Principal

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

open Classical in

noncomputable def extendRep (a : PrimeDivisor X → X.functionField) (x : X) : X.functionField :=
  if h : ringKrullDim (X.presheaf.stalk x) = 1 then a (PrimeDivisor.ofPoint x h) else 0

lemma quot_eq_zero_of_not_primeDivisor {x : X} (hx : ¬ ringKrullDim (X.presheaf.stalk x) = 1)
    (q : X.functionField ⧸ pointSubgroup D x) : q = 0 := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [QuotientAddGroup.eq_zero_iff, mem_pointSubgroup_iff]
  exact fun h => absurd h hx

lemma mk_extendRep_mem (a : repartitions k X) :
    (fun z : (⊤ : X.Opens) =>
      (QuotientAddGroup.mk (extendRep a.1 z.1) : X.functionField ⧸ pointSubgroup D z.1)) ∈
      quotSections D ⊤ := by
  intro y
  refine ⟨⊤, trivial, ?_⟩
  have hfin : {Z : PrimeDivisor X | a.1 Z ∉ Z.divisorSubgroup D}.Finite := by
    refine (a.2.union D.support.finite_toSet).subset fun Z hZ => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Finset.mem_coe,
      Finsupp.mem_support_iff] at hc
    apply hZ
    rw [PrimeDivisor.mem_divisorSubgroup, hc.2, WithZero.exp_zero]
    exact hc.1
  have hinj : Function.Injective (fun z : (⊤ : X.Opens) => z.1) := Subtype.val_injective
  refine ((hfin.image PrimeDivisor.point).preimage hinj.injOn).subset ?_
  rintro z ⟨-, hz⟩
  by_cases h : ringKrullDim (X.presheaf.stalk z.1) = 1
  · refine ⟨PrimeDivisor.ofPoint z.1 h, fun hmem => hz ?_, rfl⟩
    rw [QuotientAddGroup.eq_zero_iff, extendRep, dif_pos h, mem_pointSubgroup_iff]
    intro h'
    exact (PrimeDivisor.mem_divisorSubgroup _ _ _).mp hmem
  · exact absurd (quot_eq_zero_of_not_primeDivisor D h _) hz

variable (k) in

noncomputable def repToQuot : repartitions k X →+ quotSections D ⊤ where
  toFun a := ⟨fun z => QuotientAddGroup.mk (extendRep a.1 z.1), mk_extendRep_mem D a⟩
  map_zero' := by
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep 0 z.1) : X.functionField ⧸ pointSubgroup D z.1) = 0
    unfold extendRep
    split_ifs <;> rfl
  map_add' a b := by
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk (extendRep (a.1 + b.1) z.1) :
      X.functionField ⧸ pointSubgroup D z.1) =
      QuotientAddGroup.mk (extendRep a.1 z.1) + QuotientAddGroup.mk (extendRep b.1 z.1)
    rw [← QuotientAddGroup.mk_add]
    unfold extendRep
    split_ifs
    · rfl
    · rw [add_zero]

lemma repToQuot_apply (a : repartitions k X) (z : (⊤ : X.Opens)) :
    (repToQuot k D a).1 z = QuotientAddGroup.mk (extendRep a.1 z.1) := rfl

end Principal

section H1

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (hX : topologicalKrullDim X ≤ 1) (D : WeilDivisor X)

variable (k) in

noncomputable def repToQuotTop : repartitions k X →+ (quotSheaf D).obj.obj (op ⊤) where
  toFun a := repToQuot k D a
  map_zero' := (repToQuot k D).map_zero
  map_add' := (repToQuot k D).map_add

noncomputable def quotDelta :
    Sheaf.H.{w'} (quotSheaf D) 0 →+ Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 :=
  H.δ.{w'} (divisorSeq_shortExact D hX) 0 1 rfl

variable (k) in

noncomputable def repartitionToH1 : repartitions k X →+ Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 1 :=
  (quotDelta hX D).comp
    ((Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop).symm.toAddMonoidHom.comp (repToQuotTop k D))

lemma repartitionToH1_apply (a : repartitions k X) :
    repartitionToH1 k hX D a = quotDelta hX D
      ((Sheaf.H.equiv₀ (quotSheaf D) isTerminalTop).symm (repToQuotTop k D a)) := rfl

end H1

end GroundTheory.Arith.SchemeCoh
