import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Filter
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Sa2Prod

section Ring

open Matrix Formalism.UG

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def trunc (d : R) (A : Matrix n n R) : Matrix n n R := 1 + d • (A - 1)

theorem trunc_one (d : R) : trunc d (1 : Matrix n n R) = 1 := by simp [trunc]

theorem trunc_mul {d : R} (hd : d * d = d) (A B : Matrix n n R) :
    trunc d A * trunc d B = trunc d (A * B) := by
  have h : (d • (A - 1)) * (d • (B - 1)) = d • ((A - 1) * (B - 1)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd]
  unfold trunc
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem cT_trunc (c : R →+* R) {d : R} (hc : c d = d) (A : Matrix n n R) :
    cT c (trunc d A) = trunc d (cT c A) := by
  ext i j
  simp only [cT, trunc, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_add, map_mul, map_sub, hc]
  have : ∀ p q : n, c ((1 : Matrix n n R) p q) = (1 : Matrix n n R) q p := by
    intro p q
    by_cases h : p = q
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  rw [this]

end Ring

section Main

open GlobalTheory.Published.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Main

section Main2

open GlobalTheory.Published.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Main2

end GlobalTheory.CompanionTheory.Sa2Prod
