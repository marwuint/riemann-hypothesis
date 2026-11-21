import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial LaurentPolynomial

namespace DiagonalQuotient

variable (R : Type) [CommRing R]

noncomputable def diagEval : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval fun _ => Polynomial.X

noncomputable def diagToPoly : (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R) →ₐ[R] Polynomial R :=
  Ideal.Quotient.liftₐ (diagonalIdeal R) (diagEval R) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [diagEval])

noncomputable def polyToDiag : Polynomial R →ₐ[R] (MvPolynomial (Fin 2) R ⧸ diagonalIdeal R) :=
  Polynomial.aeval (Ideal.Quotient.mk (diagonalIdeal R) (X 0))

@[simp] lemma diagToPoly_mk (p : MvPolynomial (Fin 2) R) :
    diagToPoly R (Ideal.Quotient.mk _ p) = diagEval R p := rfl

@[simp] lemma diagEval_X (i : Fin 2) : diagEval R (X i) = Polynomial.X := by
  simp [diagEval]

noncomputable def mixedEval : MvPolynomial (Fin 2) R →ₐ[R] LaurentPolynomial R :=
  MvPolynomial.aeval ![T 1, T (-1)]

noncomputable def mixedToLaurent :
    (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) →ₐ[R] LaurentPolynomial R :=
  Ideal.Quotient.liftₐ (mixedDiagonalIdeal R) (mixedEval R) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have : (T 1 : LaurentPolynomial R) * T (-1) = 1 := by rw [← T_add]; simp
    simp [mixedEval, this])

noncomputable def mixedUnit : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ where
  val := Ideal.Quotient.mk _ (X 0)
  inv := Ideal.Quotient.mk _ (X 1)
  val_inv := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (mixedDiagonalIdeal R)), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-1, by ring⟩
  inv_val := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (mixedDiagonalIdeal R)), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-1, by ring⟩

@[simp] lemma mixedToLaurent_mk (p : MvPolynomial (Fin 2) R) :
    mixedToLaurent R (Ideal.Quotient.mk _ p) = mixedEval R p := rfl

@[simp] lemma mixedEval_X_zero : mixedEval R (X 0) = T 1 := by simp [mixedEval]

@[simp] lemma mixedEval_X_one : mixedEval R (X 1) = T (-1) := by simp [mixedEval]

@[simp] lemma mixedUnit_val : ((mixedUnit R : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ) :
    MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) = Ideal.Quotient.mk _ (X 0) := rfl

@[simp] lemma mixedUnit_inv_val : (((mixedUnit R)⁻¹ : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ) :
    MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) = Ideal.Quotient.mk _ (X 1) := rfl

noncomputable def laurentToMixed :
    LaurentPolynomial R →ₐ[R] (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) :=
  { LaurentPolynomial.eval₂ (algebraMap R _) (mixedUnit R) with
    commutes' := fun r => by
      show LaurentPolynomial.eval₂ _ _ (algebraMap R (LaurentPolynomial R) r) = _
      rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C] }

@[simp] lemma laurentToMixed_alt (n : ℤ) :
    laurentToMixed R (T n) = ((mixedUnit R ^ n : (MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R)ˣ) :
      MvPolynomial (Fin 2) R ⧸ mixedDiagonalIdeal R) :=
  LaurentPolynomial.eval₂_T _ _ n

@[simp] lemma laurentToMixed_C (a : R) :
    laurentToMixed R (LaurentPolynomial.C a) = algebraMap R _ a := by
  rw [LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes]

end DiagonalQuotient

end GroundTheory.Heights₂.Heights.FlagBundles
