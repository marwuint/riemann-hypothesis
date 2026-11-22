import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S
open GlobalTheory.DSSU (SUJ)
open GlobalTheory.SqIntSU (scalarMul unitScalar)

noncomputable section

namespace GlobalTheory.ExtChar

variable {n : ℕ} (ε : Fin n → Bool)

theorem det_unitScalar_mul (z : Circle) (x : UJ ε) :
    (umat (unitScalar ε z * x)).det = (z : ℂ) ^ n * (umat x).det := by
  show ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * umat x).det = _
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul, Fintype.card_fin]

variable [NeZero n]

theorem toCircle_pow (j : ZMod n) : ((ZMod.toCircle j : Circle) : ℂ) ^ n = 1 := by
  have h : (ZMod.toCircle j : Circle) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
  rw [← Circle.coe_pow, h, Circle.coe_one]

def cen (j : ZMod n) : SUJ ε :=
  ⟨unitScalar ε (ZMod.toCircle j)⁻¹, by
    show (umat (unitScalar ε (ZMod.toCircle j)⁻¹)).det = 1
    have h := det_unitScalar_mul ε (ZMod.toCircle j)⁻¹ 1
    rw [mul_one] at h
    rw [h, Circle.coe_inv, inv_pow, toCircle_pow, inv_one, one_mul]
    exact Matrix.det_one⟩

end GlobalTheory.ExtChar

namespace GlobalTheory.ExtChar

end GlobalTheory.ExtChar
