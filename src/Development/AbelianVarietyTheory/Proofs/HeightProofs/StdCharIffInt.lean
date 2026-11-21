import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

def leftMul (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) :
    Matrix (Fin a) (Fin b) R ≃ₗ[R] Matrix (Fin a) (Fin b) R where
  toFun x := Jiᵀ * x
  invFun y := Jᵀ * y
  map_add' := Matrix.mul_add _
  map_smul' c x := Matrix.mul_smul _ c x
  left_inv x := by
    change Jᵀ * (Jiᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    change Jiᵀ * (Jᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, mul_eq_one_comm.1 h1, Matrix.transpose_one, Matrix.one_mul]

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

end GlobalTheory.DualPairCompare

end
