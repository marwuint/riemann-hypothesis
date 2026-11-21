import Mathlib

noncomputable section

namespace Formalism.MainNotions.BridgeNGLQ

open MeasureTheory Matrix
open scoped ENNReal

def HaarScalingSplit : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F],
    ∀ (n m : ℕ) (A₁ A₂ : GL (Fin m) F) (c₁ c₂ : ℝ≥0∞),
      (∃ μ : Measure F, μ.IsAddHaarMeasure ∧ ∀ T : Set F, MeasurableSet T →
          μ ((fun y => (A₁ : Matrix (Fin m) (Fin m) F).det * y) '' T) = c₁ * μ T) →
      (∃ μ : Measure F, μ.IsAddHaarMeasure ∧ ∀ T : Set F, MeasurableSet T →
          μ ((fun y => (A₂ : Matrix (Fin m) (Fin m) F).det * y) '' T) = c₂ * μ T) →
      (∀ [MeasurableSpace (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F)]
          [BorelSpace (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F)]
          (ν : Measure (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F)), ν.IsAddHaarMeasure →
          ∀ S : Set (Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F), MeasurableSet S →
            ν ((fun X => (X.1 * (A₁ : Matrix (Fin m) (Fin m) F), X.2 * (A₂ : Matrix (Fin m) (Fin m) F))) '' S)
              = (c₁ * c₂) ^ n * ν S) ∧
      (∀ [MeasurableSpace (Matrix (Fin m) (Fin m) F)] [BorelSpace (Matrix (Fin m) (Fin m) F)]
          (ν : Measure (Matrix (Fin m) (Fin m) F)), ν.IsAddHaarMeasure →
          ∀ S : Set (Matrix (Fin m) (Fin m) F), MeasurableSet S →
            ν ((fun H => (A₂ : Matrix (Fin m) (Fin m) F)ᵀ * H * (A₁ : Matrix (Fin m) (Fin m) F)) '' S)
              = (c₁ * c₂) ^ m * ν S)

open Classical in

def HermitianQuadricInertCount : Prop :=
  ∀ (F K : Type) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K],
    Module.finrank F K = 2 →
    ∀ (d : ℕ), 1 ≤ d → ∀ (H : Matrix (Fin d) (Fin d) K),
      (∀ i j, H j i = H i j ^ Fintype.card F) → H.det ≠ 0 →
      ∀ c : F,
        (Nat.card {y : Fin d → K //
            ∑ i, ∑ j, y i ^ Fintype.card F * H i j * y j = algebraMap F K c} : ℤ) =
          if c = 0 then
            (Fintype.card F : ℤ) ^ (2 * d - 1) +
              (-1) ^ d * ((Fintype.card F : ℤ) ^ d - (Fintype.card F : ℤ) ^ (d - 1))
          else (Fintype.card F : ℤ) ^ (2 * d - 1) - (-1) ^ d * (Fintype.card F : ℤ) ^ (d - 1)

open Classical in

def HermitianQuadricSplitCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (d : ℕ), 1 ≤ d → ∀ (M : Matrix (Fin d) (Fin d) F),
    M.det ≠ 0 → ∀ c : F,
      (Nat.card {y : (Fin d → F) × (Fin d → F) // ∑ i, ∑ j, y.2 i * M i j * y.1 j = c} : ℤ) =
        if c = 0 then
          (Fintype.card F : ℤ) ^ (2 * d - 1) + (Fintype.card F : ℤ) ^ d - (Fintype.card F : ℤ) ^ (d - 1)
        else (Fintype.card F : ℤ) ^ (2 * d - 1) - (Fintype.card F : ℤ) ^ (d - 1)

end Formalism.MainNotions.BridgeNGLQ
