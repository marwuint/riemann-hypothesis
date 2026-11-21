import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hHat0.equiv (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.hHat0 y A n = smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n :=
  rfl

theorem volHat.equiv (y : (Σ k, ι k) → Ω) (A : HermLine ι) (D : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.volHat y A D = arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D :=
  rfl

end Block

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
