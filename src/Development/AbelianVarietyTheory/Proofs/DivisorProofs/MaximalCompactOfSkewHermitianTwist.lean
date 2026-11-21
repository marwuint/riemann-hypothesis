import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCpt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped Matrix TensorProduct

theorem exists_congr_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) : ∃ Q : GL (Fin n) ℂ, Q.1ᴴ * P * Q.1 = 1 := by
  have hd : P.det ≠ 0 := fun h => by
    obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [e] using hpos x hx
  obtain ⟨ε, Q, hQ⟩ := Frames.exists_congr_diagonal_sign hP hd
  refine ⟨Q, hQ.trans ?_⟩
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hx : Q.1 *ᵥ (Pi.single i 1 : Fin n → ℂ) ≠ 0 := fun h => by
    have := congrArg ((Q⁻¹).1 *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simpa using congrFun this i
  have := hpos _ hx
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ] at this
  cases h : ε i
  · simp [h, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.diagonal_apply] at this
    linarith
  · simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.ThK.SqIntMaxCpt
