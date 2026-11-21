import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def HaarChart (X : Data E r) (c : ℝ≥0∞) : Prop :=
  ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ g, φ (frameOf X g) ∂haarR X = c * ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X)

def trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
    (y : Frame X.Ψ r) : Frame X'.Ψ r :=
  fun τ' => (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') : Matrix (Fin r) (Fin r) ℂ)

end

end GlobalTheory.FlagQuotHaar
