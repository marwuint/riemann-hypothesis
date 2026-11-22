import Mathlib
import Formalism.HyperbolicPlaceProducts.Statement
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def hdual {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (M : AddSubgroup U) : AddSubgroup U where
  carrier := {x | ∀ y ∈ M, h x y ∈ O}
  add_mem' := by
    intro a b ha hb y hy
    simpa using O.add_mem (ha y hy) (hb y hy)
  zero_mem' := by
    intro y _
    simp
  neg_mem' := by
    intro a ha y hy
    simpa using O.neg_mem (ha y hy)

def DualIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [FiniteDimensional E U] (h : U →ₗ[E] U →ₗ⋆[E] E)
    (M N : Submodule (𝓞 E) U), (∀ x : U, (∀ y : U, h x y = 0) → x = 0) → N ≤ M → M.FG →
    Submodule.span E (N : Set U) = ⊤ →
      (hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).relIndex
          (hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) =
        N.toAddSubgroup.relIndex M.toAddSubgroup

end Formalism.HermitianLatticeCounting.S6
