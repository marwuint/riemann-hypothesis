import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.UnitaryMatrixFamily

variable {n : ℕ} {ε : Fin n → Bool}

theorem umat_mul (a b : UJ ε) : umat (a * b) = umat a * umat b := rfl

theorem umat_one : umat (1 : UJ ε) = 1 := rfl

end GlobalTheory.SepReal.UnitaryMatrixFamily

namespace GlobalTheory.SepReal.CoefProjProof

end GlobalTheory.SepReal.CoefProjProof

namespace GlobalTheory.SepReal.CoefProjProof

end GlobalTheory.SepReal.CoefProjProof

namespace GlobalTheory.SepReal.CoefProjProof

end GlobalTheory.SepReal.CoefProjProof
