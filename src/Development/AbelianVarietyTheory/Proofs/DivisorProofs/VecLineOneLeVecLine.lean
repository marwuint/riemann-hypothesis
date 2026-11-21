import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisUnfold

open GlobalTheory.EisMidHt (adVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in
theorem inv_mulVec_cancel (p : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J p⁻¹).1 *ᵥ (matHom _ σ J p).1 *ᵥ y = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

def vecStab (z : Fin n → AF F ⊗[F] E) (H : Subgroup (AF F ⊗[F] E)ˣ) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l ∈ H, (matHom _ σ J p).1 *ᵥ z = l.1 • z}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro p q ⟨l, hl, e⟩ ⟨l', hl', e'⟩
    refine ⟨l * l', mul_mem hl hl', ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_smul, e, smul_smul, Units.val_mul, mul_comm]
  inv_mem' := by
    rintro p ⟨l, hl, e⟩
    refine ⟨l⁻¹, inv_mem hl, ?_⟩
    have h := inv_mulVec_cancel σ J p z
    rw [e, Matrix.mulVec_smul] at h
    conv_rhs => rw [← h, smul_smul, Units.inv_mul, one_smul]

def vecLineOne (z : Fin n → AF F ⊗[F] E) : Subgroup (GAd σ J) := vecStab σ J z (absE F E).ker

variable {σ J}

theorem mem_vecLineOne {z : Fin n → AF F ⊗[F] E} {p : GAd σ J} :
    p ∈ vecLineOne σ J z ↔ ∃ l : (AF F ⊗[F] E)ˣ, absE F E l = 1 ∧ (matHom _ σ J p).1 *ᵥ z = l.1 • z := Iff.rfl

end GlobalTheory.EisUnfold

end
