import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurvePlaces
import GroundTheory.FunctionField.Divisor
set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology Module

open scoped WithZero

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor

noncomputable def degree (Z : PrimeDivisor X) : ℕ :=
  finrank k (IsLocalRing.ResidueField (X.presheaf.stalk Z.point))

end PrimeDivisor

noncomputable def WeilDivisor.degree : WeilDivisor X →+ ℤ :=
  Finsupp.liftAddHom fun Z => AddMonoidHom.mulRight ((Z.degree (k := k) : ℕ) : ℤ)

variable [IsProper (X ↘ Spec (.of k))]

noncomputable def divisorEquiv (hX : topologicalKrullDim X ≤ 1) :
    WeilDivisor X ≃+ Divisor k X.functionField :=
  Finsupp.domCongr (placeEquiv hX)

@[simp]
lemma divisorEquiv_apply_toPlace (hX : topologicalKrullDim X ≤ 1) (D : WeilDivisor X)
    (Z : PrimeDivisor X) : divisorEquiv (k := k) hX D Z.toPlace = D Z := by
  change Finsupp.equivMapDomain (placeEquiv hX) D (placeEquiv (k := k) hX Z) = D Z
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

variable [IsFunctionField k X.functionField]

end GroundTheory.Arith.SchemeCoh
