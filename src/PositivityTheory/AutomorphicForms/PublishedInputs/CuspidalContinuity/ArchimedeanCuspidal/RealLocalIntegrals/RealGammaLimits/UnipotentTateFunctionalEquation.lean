import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped FourierTransform

namespace Ad3.LR.C

def cr (e : Bool) (s : ℂ) (r : ℝ) : ℂ := (if e ∧ r < 0 then -1 else 1) * ((|r| : ℝ) : ℂ) ^ s

def pI (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (u : ℝ) (p : M22 × (Fin 2 → ℝ)) : ℂ :=
  Wm k (Matrix.of p.1)⁻¹ * sg (Matrix.of p.1).det * ((|(Matrix.of p.1).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
    cr (!δ) (s - 1) (p.2 1) * Φ (Matrix.of.symm (Matrix.of p.1 * blk p.2 * ((cyc u : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)))

def Pu (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (u : ℝ) : ℂ := ∫ p, pI k Φ δ s u p

def ge (ε u : ℝ) : ℝ := Real.exp (-Real.pi * ε ^ 2 * u ^ 2)

def Dual : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
  ∫ p : ℝˣ × ℝ, sec k Φ (mm p.1 p.2) * chR δ s p.1 ∂(mulR.prod volume) =
    gT (!δ) s * ∫ h : M22, inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * z2' k δ s (Matrix.of h)⁻¹

end Ad3.LR.C
