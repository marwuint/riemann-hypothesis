import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
import ReciprocityTheory.SemistableReduction.ShareDetA

noncomputable section

open NumberField Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul mat hermC sgn)
open ReciprocityTheory.ChartRestriction.G
open scoped ComplexOrder

namespace GlobalTheory.FrameLog

variable {N : ℕ}

def Par (p : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  g.det ≠ 0 ∧ ∀ a c : Fin N, (c : ℕ) < p → ¬ (a : ℕ) < p → g a c = 0

theorem Par.mul {p : ℕ} {g h : Matrix (Fin N) (Fin N) ℂ} (hg : Par p g) (hh : Par p h) : Par p (g * h) := by
  refine ⟨by rw [det_mul]; exact mul_ne_zero hg.1 hh.1, fun a c hc ha => ?_⟩
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < p
  · rw [hg.2 a k hk ha, zero_mul]
  · rw [hh.2 k c hc hk, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E N)

variable {X}

def ofMat (m : X.Ψ → Matrix (Fin N) (Fin N) ℂ) : Frame X.Ψ N := fun τ i j => m τ i j

theorem mat_rmul (x b : Frame X.Ψ N) (τ : X.Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

end GlobalTheory.FrameLog
