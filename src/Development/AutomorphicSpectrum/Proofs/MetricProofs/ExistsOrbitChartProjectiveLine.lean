import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Line

abbrev LPt : Type := (Σ _ : Unit, Fin 2) → ℂ

def lineφ (w : Fin 1 → ℂ) : LPt := fun q => ![1, w 0] q.2

@[simp] theorem lineφ_zero (w : Fin 1 → ℂ) : lineφ w ⟨(), 0⟩ = 1 := rfl

@[simp] theorem lineφ_one (w : Fin 1 → ℂ) : lineφ w ⟨(), 1⟩ = w 0 := rfl

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Line

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

end GlobalTheory.CompanionTheory.Ar.PB.WMan
