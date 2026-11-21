import Mathlib

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def CardGeneralLinear : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * (n - 1) / 2) * (Fintype.card F : ℝ) ^ (n * (n + 1) / 2) *
        ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1))

def CardUnitriangular : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ),
    Nat.card {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} =
      Fintype.card F ^ (n * (n - 1) / 2)

def EulerProductBounds : Prop :=
  ∀ (q : ℝ), 3 ≤ q → ∀ n : ℕ,
    1 / 2 ≤ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ∧ ∏ i ∈ range n, (1 - q⁻¹ ^ (i + 1)) ≤ 1

def CardStabilizerVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (v : Fin n → F), v ≠ 0 →
    Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} *
      (Fintype.card F ^ n - 1) = Fintype.card (GL (Fin n) F)

def PrimeOrderFinrank : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n g : ℕ) (A : Matrix (Fin n) (Fin n) K),
    g.Prime → A ^ g = 1 → A ≠ 1 → g - 1 ≤ Module.finrank ℚ K * n

end Formalism.LogVandermondeBounds.StandardLattice
