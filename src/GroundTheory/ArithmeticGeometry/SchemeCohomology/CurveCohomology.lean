import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCohomologySheaves
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe w' u

namespace GroundTheory.Arith.SchemeCoh

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

section Scalars

variable [IsIntegral X]

variable [IsLocallyNoetherian X] [IsNormalScheme X]

lemma PrimeDivisor.valuation_algebraMap_scalar_le_one (Z : PrimeDivisor X) (c : k) :
    Z.valuation (algebraMap k X.functionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk Z.point) X.functionField]
  exact Z.valuation_algebraMap_le_one _

lemma mul_mem_pointSubgroup (D : WeilDivisor X) (x : X) (c : k) {f : X.functionField}
    (hf : f ∈ pointSubgroup D x) : algebraMap k X.functionField c * f ∈ pointSubgroup D x := by
  rw [mem_pointSubgroup_iff] at hf ⊢
  intro h
  rw [map_mul]
  calc _ ≤ 1 * WithZero.exp (D (PrimeDivisor.ofPoint x h)) :=
        mul_le_mul' ((PrimeDivisor.ofPoint x h).valuation_algebraMap_scalar_le_one c) (hf h)
    _ = _ := one_mul _

end Scalars

section Endo

variable [IsIntegral X]

variable [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

noncomputable def quotMul (c : k) (x : X) :
    X.functionField ⧸ pointSubgroup D x →+ X.functionField ⧸ pointSubgroup D x :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (algebraMap k X.functionField c))
    (fun _ hf => mul_mem_pointSubgroup D x c hf)

lemma quotMul_mk (c : k) (x : X) (f : X.functionField) :
    quotMul D c x (QuotientAddGroup.mk f) = QuotientAddGroup.mk (algebraMap k X.functionField c * f) :=
  rfl

end Endo

noncomputable instance globalAlgebra : Algebra k Γ(X, ⊤) := (scalarRingHom X).toAlgebra

section H0

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

variable (k) in

def globalL (D : WeilDivisor X) : Submodule k X.functionField where
  carrier := {f | ∀ Z : PrimeDivisor X, Z.valuation f ≤ WithZero.exp (D Z)}
  zero_mem' := fun Z => by simp
  add_mem' {f g} hf hg := fun Z => (Valuation.map_add _ _ _).trans (max_le (hf Z) (hg Z))
  smul_mem' c {f} hf := fun Z => by
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * WithZero.exp (D Z) :=
          mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) (hf Z)
      _ = _ := one_mul _

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
lemma mem_globalL (D : WeilDivisor X) (f : X.functionField) :
    f ∈ globalL k D ↔ ∀ Z : PrimeDivisor X, Z.valuation f ≤ WithZero.exp (D Z) := Iff.rfl

end H0

end GroundTheory.Arith.SchemeCoh
