import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.Affine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Toric

universe u

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial

section HalfSpace

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)

def LowerBound (f : AddMonoidAlgebra k G) (a : ℤ) : Prop :=
  ∀ m ∈ f.coeff.support, a ≤ φ m

variable {φ}

theorem LowerBound.add {f g : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g a) : LowerBound φ (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (Finsupp.support_add (by simpa using hm)) with h | h
  · exact hf m h
  · exact hg m h

end HalfSpace

end GroundTheory.Arith.Toric
