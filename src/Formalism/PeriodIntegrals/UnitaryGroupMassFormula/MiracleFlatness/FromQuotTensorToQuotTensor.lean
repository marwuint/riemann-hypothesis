import Mathlib

universe u v

open TensorProduct

namespace PI.UnitaryGroupMassFormula.MF

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] (x : A)

lemma quot_smul_mk (a : A) (b : B) :
    (Ideal.Quotient.mk (Ideal.span {x}) a) • (Ideal.Quotient.mk ((Ideal.span {x}).map (algebraMap A B)) b) =
      Ideal.Quotient.mk _ (algebraMap A B a * b) := by
  simp [Algebra.smul_def]

variable (J : Ideal (A ⧸ Ideal.span {x}))

lemma quot_smul_J (a : A) (j : J) : (Ideal.Quotient.mk (Ideal.span {x}) a) • j = a • j := by
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]

noncomputable def toQuotTensor :
    B ⊗[A] J →+ (B ⧸ (Ideal.span {x}).map (algebraMap A B)) ⊗[A ⧸ Ideal.span {x}] J :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun j => Ideal.Quotient.mk _ b ⊗ₜ j) (fun j j' => tmul_add _ _ _))
      (fun b b' => by ext j; simp [add_tmul]))
    (fun a b j => by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, ← quot_smul_mk, smul_tmul, quot_smul_J])

@[simp] lemma toQuotTensor_tmul (b : B) (j : J) :
    toQuotTensor x J (b ⊗ₜ j) = Ideal.Quotient.mk _ b ⊗ₜ j := rfl

end PI.UnitaryGroupMassFormula.MF
