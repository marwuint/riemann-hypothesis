import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLGenPtInt

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

def qc_sh {n : ℕ} (mu : Fin n → ℤ) (ε : ℤ) : Fin n → ℤ := fun a => mu a + ε

lemma qc_colH_sh {n : ℕ} (mu : Fin n → ℤ) (ε c : ℤ) : colH (qc_sh mu ε) (c + ε) = colH mu c := by
  unfold colH qc_sh
  congr 1
  ext m
  simp

lemma qc_mem_sh (mu : Fin n → ℤ) (ε c : ℤ) : c + ε ∈ TCols (qc_sh mu ε) ↔ c ∈ TCols mu := by
  simp [TCols, qc_sh]

def qc_colE (mu : Fin n → ℤ) (ε : ℤ) : ↥(TCols mu) ≃ ↥(TCols (qc_sh mu ε)) where
  toFun c := ⟨c.1 + ε, (qc_mem_sh mu ε c.1).2 c.2⟩
  invFun c := ⟨c.1 - ε, (qc_mem_sh mu ε _).1 (by rw [sub_add_cancel]; exact c.2)⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)

lemma qc_colE_val (mu : Fin n → ℤ) (ε : ℤ) (c : ↥(TCols mu)) : ((qc_colE mu ε c : ↥(TCols (qc_sh mu ε))) : ℤ) = c.1 + ε := rfl

def qc_idxE (mu : Fin n → ℤ) (ε : ℤ) : TIdx (qc_sh mu ε) ≃ TIdx mu where
  toFun I c := ⟨(I (qc_colE mu ε c)).1, (I (qc_colE mu ε c)).2.trans (qc_colH_sh mu ε c.1)⟩
  invFun I c := ⟨(I ((qc_colE mu ε).symm c)).1, (I ((qc_colE mu ε).symm c)).2.trans (by
    have := qc_colH_sh mu ε (c.1 - ε)
    rw [sub_add_cancel] at this
    exact this.symm)⟩
  left_inv I := by
    funext c
    apply Subtype.ext
    show (I (qc_colE mu ε ((qc_colE mu ε).symm c))).1 = (I c).1
    rw [Equiv.apply_symm_apply]
  right_inv I := by
    funext c
    apply Subtype.ext
    show (I ((qc_colE mu ε).symm (qc_colE mu ε c))).1 = (I c).1
    rw [Equiv.symm_apply_apply]

lemma qc_idxE_val (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) (c : ↥(TCols mu)) :
    (qc_idxE mu ε I c).1 = (I (qc_colE mu ε c)).1 := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
