import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

section Mat

variable {R : Type*} [CommRing R]

def w3 : GL (Fin 3) R :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def ti {n : Type*} [Fintype n] [DecidableEq n] (g : GL n R) : GL n R :=
  ⟨g.inv.transpose, g.val.transpose, by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one]⟩

end Mat

end Ad3.K.QuadraticBaseChangeGL3
