import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
import Formalism.GradedWeylDivisibility.FinalB

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

variable {n : ℕ}

def qd_sig (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ →ₐ[ℚ] GLCoord ℚ n :=
  (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)).comp (rename Prod.swap)

variable [NeZero n]

def qd_U (mu : Fin n → ℤ) : GLCoord ℚ n := mapCoord ℚ ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)

def qd_L (mu : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] GLCoord ℚ n :=
  (LinearMap.mulLeft ℚ (qd_U mu)) ∘ₗ (qd_sig n).toLinearMap

lemma qd_L_apply (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    qd_L mu P = qd_U mu * qd_sig n P := rfl

omit [NeZero n] in
lemma generic_point_det_isUnit (n : ℕ) : IsUnit (Matrix.of fun a b : Fin n =>
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))).det := by
  have : (Matrix.of fun a b : Fin n =>
      Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))) =
      (Polynomial.C.comp (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n))).mapMatrix (genMat ℚ n) := by
    ext a b : 2; simp [genMat]
  rw [this, ← RingHom.map_det]
  exact (IsLocalization.Away.algebraMap_isUnit (S := GLCoord ℚ n) (genMat ℚ n).det).map Polynomial.C

def qd_genPt (n : ℕ) : GL (Fin n) (Polynomial (GLCoord ℚ n)) :=
  Matrix.GeneralLinearGroup.mk'' _ (generic_point_det_isUnit n)

omit [NeZero n] in
lemma qd_genPt_val (i j : Fin n) : (qd_genPt n).val i j =
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (i, j))) := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
