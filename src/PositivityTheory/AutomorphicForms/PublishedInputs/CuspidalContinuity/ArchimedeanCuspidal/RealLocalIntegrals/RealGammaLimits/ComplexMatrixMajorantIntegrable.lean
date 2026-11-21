import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Z2

noncomputable section

open MeasureTheory Complex

namespace Ad3.LR.C

def prI (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (p : ℝˣ × M22) : ℂ :=
  Wm k (d2 p.1 * (Matrix.of p.2)⁻¹) * inn Φ 1 (Matrix.of p.2) * sg (Matrix.of p.2).det *
    ((|(Matrix.of p.2).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * chR δ (s - 1 / 2) p.1

def Prim : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (δ : Bool) (s : ℂ), 0 < s.re → s.re < 1 →
  ∫ a, sec k Φ (dg a 1 1) * chR δ (s - 1) a ∂mulR =
    ∫ h : M22, inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * z2 k δ s (Matrix.of h)⁻¹

end Ad3.LR.C
