import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.B

def eta (h : M22) : Fin 2 → ℝ := fun j => (Matrix.of h)⁻¹ 1 j

def rt (g : GL (Fin 3) ℝ) (Ψ : M23 → ℂ) (X : M23) : ℂ :=
  Ψ (Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ)))

def pol (i j : Fin 3) (Ψ : M23 → ℂ) (X : M23) : ℂ :=
  fderiv ℝ Ψ X (Matrix.of.symm (Matrix.of X * Matrix.single i j (1 : ℝ))) + if i = j then Ψ X else 0

def maj (k N : ℕ) (a b : ℝ) (h : M22) : ℝ :=
  ‖Wm k (Matrix.diagonal ![a, 1] * (Matrix.of h)⁻¹)‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) /
    ((1 + ‖h‖) ^ N * (1 + |b| * ‖eta h‖) ^ N)

end Ad3.LR.B
