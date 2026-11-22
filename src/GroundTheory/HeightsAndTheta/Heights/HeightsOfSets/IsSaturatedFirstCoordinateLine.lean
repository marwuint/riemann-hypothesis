import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section HeightObjects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def height (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (A : HermLine ι)
    (W : Ideal (MRing ι)) : ℝ :=
  I W 1 ![A] / degC W

variable {Ω : Type*} [Field Ω]

end HeightObjects

def HeightComparison.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (A H : HermLine ι),
    IsIntersectionFamily I → IsSmoothHerm A → IsSmoothHerm H → H.a = 1 →
    ∃ (k : ℕ) (C : ℝ), ∀ W : Ideal (MRing ι), IsArithVar W 1 →
      |height I A W| ≤ (k : ℝ) * height I H W + C

def DenseBoundedHeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (D : ℕ)
    (H : HermLine ι),
    IsIntersectionFamily I → IsArithVar P (D + 1) → IsSmoothHerm H → H.a = 1 →
    ∃ (C : ℝ) (F : Set (Ideal (MRing ι))), IsZariskiDense P F ∧
      ∀ W ∈ F, IsArithVar W 1 ∧ P ≤ W ∧ height I H W ≤ C

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
