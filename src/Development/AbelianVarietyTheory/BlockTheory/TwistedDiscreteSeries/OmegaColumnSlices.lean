import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Line
variable {k : Type} [Field k] {n n' : Type}

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n]

def omCol (μz : kˣ →* ℂˣ) (h : GL n k) (φ : (n → k) → ℂ) : (n → k) → ℂ := fun y =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * φ ((h⁻¹).val *ᵥ y)

def omRow (μz : kˣ →* ℂˣ) (h : GL n k) (φ' : (n → k) → ℂ) : (n → k) → ℂ := fun η =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ' (η ᵥ* h.val)

end Line

end GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
