import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DoubleBlock
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Filter Topology
open scoped Manifold ContDiff ENNReal

noncomputable section

section OneBlock

variable {κ : Type} [Fintype κ]

def IsAnalyticSubset (D : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Fin D → ℂ) M]
    (A : Set M) : Prop :=
  IsClosed A ∧ ∀ q : M, ∃ U ∈ 𝓝 q, ∃ (r : ℕ) (g : Fin r → M → ℂ),
    (∀ j, MDifferentiableOn 𝓘(ℂ, Fin D → ℂ) 𝓘(ℂ, ℂ) (g j) U) ∧
      A ∩ U = {q' | q' ∈ U ∧ ∀ j, g j q' = 0}

end OneBlock

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def hHat0 (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) : ℝ :=
  smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n

def volHat (y : (Σ k, ι k) → Ω) (A : HermLine ι) (D : ℕ) : ℝ :=
  arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

end Block

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
