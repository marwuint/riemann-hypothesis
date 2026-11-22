import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace Ad3.K.LC.B

abbrev E5 : Type := M23 × (Fin 2 → ℂ)

def rt (g : GL (Fin 3) ℂ) (Ψ : E5 → ℂ) (X : E5) : ℂ :=
  Ψ (Matrix.of.symm (Matrix.of X.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), X.2)

def eta (h : M22) : Fin 2 → ℂ := fun j => (Matrix.of h)⁻¹ 1 j

end Ad3.K.LC.B
