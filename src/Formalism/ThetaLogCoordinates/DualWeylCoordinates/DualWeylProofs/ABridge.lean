import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaExpEqBidetExp

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qa_can_emb {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2
    (f := fun a : Fin (colH mu c) => Fin.castLE (colH_le mu c) a) (by intro x; simp [canT])
    (Fin.strictMono_castLE _)
  exact (congrFun this a).symm

lemma qa_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (initMinor R (qa_row I c) (colH_le mu c)) := by
  conv_rhs => rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [Matrix.transpose_apply, genMat, qa_row, qa_can_emb]

lemma qa_prod_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (qa_P R I) := by
  unfold qa_P
  rw [map_prod]
  exact Finset.prod_congr rfl fun c _ => qa_minor R I c

theorem qa_brkPol_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brkPol mu I = (genMat ℤ n).det ^ (mu (lastIdx n)).toNat * rename Prod.swap (qa_P ℤ I) := by
  unfold brkPol
  rw [qa_prod_minor]

def qa_Phi (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
  (LinearMap.mulLeft R u) ∘ₗ (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap ∘ₗ
    (rename (R := R) (Prod.swap : Fin n × Fin n → Fin n × Fin n)).toLinearMap

lemma qa_Phi_apply (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) (f : MvPolynomial (Fin n × Fin n) R) :
    qa_Phi R n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (rename Prod.swap f) := rfl

def qa_intLin {M N : Type*} [AddCommGroup M] {i1 : Module ℤ M} [AddCommGroup N] {i2 : Module ℤ N}
    (f : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 i2) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) ⟨f, f.map_add⟩
    (fun z x => (f.map_smul z x).trans (int_smul_eq_zsmul i2 z (f x)))

def qa_PhiZ (n : ℕ) (u : GLCoord ℤ n) := qa_intLin (qa_Phi ℤ n u)

lemma qa_PhiZ_apply (n : ℕ) (u : GLCoord ℤ n) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    qa_PhiZ n u f = u * algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap f) := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
