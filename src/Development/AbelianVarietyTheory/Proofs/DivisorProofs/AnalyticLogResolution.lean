import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions

namespace GlobalTheory.LogResInt

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open scoped ENNReal

noncomputable section

variable {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def chartSumInt (B : FinHolAtlas n Y) (Φ : LocPot Y) (U : Set Y) (f : Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    f ((B.chart j).symm w) * ‖locDens B (fun _ => Φ) j w‖ₑ

def IsJointSNC (B : FinHolAtlas n Y) (μ : Y → X) {q r : ℕ} (L : Fin q → LocPot X)
    (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) : Prop :=
  ∀ y, ∃ χ : OpenPartialHomeomorph Y (Fin n → ℂ), IsCompatChart B χ ∧ y ∈ χ.source ∧
    ∃ κ : Fin r → Option (Fin n), (∀ k k' a, κ k = some a → κ k' = some a → k = k') ∧
      (∀ k, W k ∩ χ.source = {w ∈ χ.source | ∃ a, κ k = some a ∧ χ w a = 0}) ∧
      ∀ i, χ.source ⊆ μ ⁻¹' (L i).U (μ y) ∧ ∃ u : Y → ℂ, B.HoloOn χ.source u ∧
        (∀ w ∈ χ.source, u w ≠ 0) ∧
        ∀ w ∈ χ.source, t i (μ y) (μ w) = u w * ∏ k, (match κ k with
          | some a => χ w a ^ e i k
          | none => 1)

end

end GlobalTheory.LogResInt
