import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar unitScalar)

noncomputable section

namespace GlobalTheory.ExtCharCont

open GlobalTheory.ExtChar Polynomial

variable {n : ℕ} (ε : Fin n → Bool)

theorem umat_mul' (a b : UJ ε) : umat (a * b) = umat a * umat b := rfl

variable [NeZero n]

end GlobalTheory.ExtCharCont

end
