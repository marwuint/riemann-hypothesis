import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.QuotEqZeroOfNotPrimeDivisor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCanonical
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Module MonoidalCategory

universe w' u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

variable [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [IsNormalScheme X]

section Instances

variable (hX : topologicalKrullDim X = 1)

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
include hX in

theorem curve_instances :
    IsNoetherian X ∧ IsLocallyFactorial X ∧ IsFunctionField k X.functionField := by
  have : IsNoetherian X := isNoetherian_of_finiteType (k := k) X
  exact ⟨this, isLocallyFactorial_of_dim_le_one hX.le, isFunctionField X hX⟩

end Instances

section Canonical

noncomputable def omega (hX : topologicalKrullDim X = 1) : X.Modules :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  haveI := (curve_instances (k := k) hX).2.2
  canonicalSheaf (k := k) hX.le

end Canonical

end GroundTheory.Arith.SchemeCoh
