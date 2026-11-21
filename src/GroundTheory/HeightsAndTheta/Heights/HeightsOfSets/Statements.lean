import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Points
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

def HeightComparison.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A : HermLine n),
    ∃ (k : ℕ) (C : ℝ), ∀ x ∈ P.points (AlgebraicClosure ℚ),
      |height A x| ≤ k * height (HermLine.standard n) x + C

def DenseBoundedHeight.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n),
    ∃ (S : Set (Cone n (AlgebraicClosure ℚ))) (C : ℝ), S ⊆ P.points (AlgebraicClosure ℚ) ∧
      P.ZariskiDense S ∧ ∀ x ∈ S, height (HermLine.standard n) x ≤ C

def SlopeMaxExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E' E E'' : HermitianBundle.{0} K),
    HermitianExtension E' E E'' → E.slopeMax ≤ max E'.slopeMax E''.slopeMax

end

end GroundTheory.Heights₂.Heights
