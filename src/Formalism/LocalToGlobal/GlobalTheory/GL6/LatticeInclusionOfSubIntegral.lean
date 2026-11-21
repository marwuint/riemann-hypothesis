import Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionFamilyOf

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

def bwA_N {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => if τ = τv then atInf (embT D) (B'⁻¹ * B : GL (Fin n) D.host.E).1 τ else 1

theorem bwA_N_mul {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    (fun τ => bwA_N D τv B B' τ * atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ) =
      fun τ => if τ = τv then atInf (embT D) (B'⁻¹ : GL (Fin n) D.host.E).1 τ
        else atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ := by
  funext τ
  unfold bwA_N
  split_ifs with h
  · simp only [atInf]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  · rw [one_mul]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
