import Mathlib
import Formalism.HyperbolicPlaceProducts.Statement
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def IotaDual : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (g : K) (L₀ L₀' : AddSubgroup U) (ι' : U → U),
    g ∈ O → star g = g → g ≠ 0 → (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ O) → (∀ x ∈ L₀', ι' x ∈ L₀) →
    (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ O, h (ι' x) (ι' y) - h x y = g * t) →
      (∀ l' ∈ L₀', ∀ x ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' x - x = g • l) → h (g⁻¹ • (l' - ι' l')) x ∈ O) ∧
      (∀ l' ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' l' - l' = g • l) → g⁻¹ • (l' - ι' l') ∈ L₀)

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
