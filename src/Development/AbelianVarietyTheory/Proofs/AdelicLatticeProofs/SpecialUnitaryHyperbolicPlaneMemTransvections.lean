import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.NontrivialTransvection
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Plane
open GlobalTheory.UTrans.Model

variable {E : Type} [Field E] {n : ℕ}

def what₂ (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (z w : Fin n → E) : Matrix (Fin 2) (Fin n) E :=
  Matrix.of fun i b => ![∑ e, G b e * σ (w e), ∑ e, G b e * σ (z e)] i

end GlobalTheory.UTrans.Plane
