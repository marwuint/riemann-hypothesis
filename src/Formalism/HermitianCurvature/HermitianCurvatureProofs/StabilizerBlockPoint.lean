import Formalism.HermitianCurvature.StatementG

open Matrix
open Formalism.FourierDecayAlt.G

namespace Formalism.FourierDecayAlt.P.G4

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  simp [blk, h]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  have h : ∀ i : Fin n, finSumFinEquiv.symm (i.castSucc : Fin (n+1)) = Sum.inl i := fun i =>
    finSumFinEquiv_symm_apply_castAdd (n := 1) i
  have h2 : finSumFinEquiv.symm (Fin.last n : Fin (n+1)) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
  simp [blk, h, h2]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem upperUni_det {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u.det = 1 := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hu.1]

theorem superSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    superSum (blk A b a e) = superSum A + b (Fin.last m) := by
  unfold superSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_cl]

theorem subSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    subSum (blk A b a e) = subSum A + a (Fin.last m) := by
  unfold subSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_lc]

end Formalism.FourierDecayAlt.P.G4

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
