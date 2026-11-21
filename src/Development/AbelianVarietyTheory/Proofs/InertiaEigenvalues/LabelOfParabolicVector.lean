import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelMulOfConstituentStatement

noncomputable section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
namespace GlobalTheory.GLp.ParLabel

section Blocks
variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

def sp (M : Mt g (a + b)) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (ZMod g) := M.submatrix finSumFinEquiv finSumFinEquiv

theorem sp_mul (M N : Mt g (a + b)) : sp (M * N) = sp M * sp N := by
  simp [sp, Matrix.submatrix_mul_equiv]

theorem tl_eq (M : Mt g (a + b)) : tl a M = (sp M).toBlocks₁₁ := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [tl, entN, sp, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem br_eq (M : Mt g (a + b)) : br a b M = (sp M).toBlocks₂₂ := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [br, entN, sp, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_right]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem inPar_iff (M : Mt g (a + b)) : InPar a M ↔ (sp M).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    have hi' := i.2
    have := congrFun (congrFun h ⟨i - a, by omega⟩) ⟨j, hj⟩
    simp only [sp, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Matrix.zero_apply] at this
    convert this using 2 <;> ext <;> simp <;> omega

def Over (p : Gn g (a + b)) (x : Gn g a) (y : Gn g b) : Prop :=
  InPar a (p : Mt g (a + b)) ∧ tl a (p : Mt g (a + b)) = (x : Mt g a) ∧ br a b (p : Mt g (a + b)) = (y : Mt g b)

theorem over_iff (p : Gn g (a + b)) (x : Gn g a) (y : Gn g b) :
    Over p x y ↔ ∃ Z, sp (p : Mt g (a + b)) = Matrix.fromBlocks (x : Mt g a) Z 0 (y : Mt g b) := by
  rw [Over, inPar_iff, tl_eq, br_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨_, by rw [← h1, ← h2, ← h3, Matrix.fromBlocks_toBlocks]⟩
  · rintro ⟨Z, h⟩
    rw [h]
    simp

theorem Over.mul {p q : Gn g (a + b)} {x x' : Gn g a} {y y' : Gn g b} (h : Over p x y) (h' : Over q x' y') :
    Over (p * q) (x * x') (y * y') := by
  rw [over_iff] at *
  obtain ⟨Z, h⟩ := h
  obtain ⟨Z', h'⟩ := h'
  refine ⟨(x : Mt g a) * Z' + Z * (y' : Mt g b), ?_⟩
  rw [Units.val_mul, sp_mul, h, h']
  simp [Matrix.fromBlocks_multiply]

end Blocks

end GlobalTheory.GLp.ParLabel
