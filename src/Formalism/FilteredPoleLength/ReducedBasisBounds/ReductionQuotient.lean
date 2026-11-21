import Mathlib
import Formalism.LogFactorialIndices.StatementIdx

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Polynomial
open scoped ComplexOrder

def QuotientLength : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (c : V →ₗ[K] (Fin n → K)) (N : Submodule K V),
    LinearMap.ker c ≤ N → ∀ (X : Submodule O V) (e be : ℕ) (th : Fin n → V),
    (∀ x ∈ X, ∀ i, ∃ a : O, c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a) →
    (∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X) →
    ∀ a a' : O, a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
      let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
      ∃ m : ℕ, Module.length O (↥X ⧸ ((X ⊓ N.restrictScalars O) ⊔ Tj).comap X.subtype) = m ∧
        (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)

def PoleOrderGood : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ) (e : ℤ), 1 ≤ ep → 0 ≤ c' → 0 ≤ vet →
    ν ≤ νs + c' * vet → (∃ n : ℤ, (ep : ℝ) * ν = n) → (T : ℝ) * νs ≤ e →
      ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def PoleOrderBad : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ), 1 ≤ ep → 1 ≤ T → 0 ≤ c' → 0 ≤ vet → ν ≤ νs + c' * vet →
    let e : ℤ := ⌈(T : ℝ) * (νs + 1)⌉
    ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def LevelsSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (mm : ι → ℤ) (v : ι → ℝ) (T : ℕ) (c' : ℝ),
    (∀ z, (mm z : ℝ) ≤ ep z * T * c' * v z) →
      ∑ z, (mm z : ℝ) * f z ≤ T * c' * ∑ z, ((ep z : ℝ) * f z) * v z

end Formalism.LatticeBaseChangeAlt
