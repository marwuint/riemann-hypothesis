import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsAnalyticSubset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine

namespace GlobalTheory

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology

noncomputable section

namespace AnDim

variable {d : ℕ} {X : Type} [TopologicalSpace X]

def singularLocus (A : FinHolAtlas d X) (T : Set X) : Set X :=
  T \ ⋃ n, regularLocus A T n

def analyticDim (A : FinHolAtlas d X) (T : Set X) : WithBot ℕ∞ :=
  ⨆ (n : ℕ) (_ : (regularLocus A T n).Nonempty), (n : WithBot ℕ∞)

end AnDim

namespace Published

open AnDim

def AnalyticSetDimension : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    (∀ T : Set X, A.IsAnalyticSubset T →
      A.IsAnalyticSubset (singularLocus A T) ∧
        (T.Nonempty → analyticDim A (singularLocus A T) < analyticDim A T)) ∧
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      analyticDim A Z = n) ∧
    (∀ C S : Set X, IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      analyticDim A (C ∩ S) < analyticDim A C) ∧
    (∀ T : Set X, A.IsAnalyticSubset T →
      {C | IsIrreducibleComponent A T C}.Finite ∧ T = ⋃₀ {C | IsIrreducibleComponent A T C})

end Published

namespace AnDim

end AnDim

end

end GlobalTheory
