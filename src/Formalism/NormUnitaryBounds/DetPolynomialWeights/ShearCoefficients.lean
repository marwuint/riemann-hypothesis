import Formalism.NormUnitaryBounds.Statement

open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

namespace ShearCoefficients

variable {R : Type*} [CommRing R]

def CoeffHom {σ M : Type*} [AddCommMonoid M] (wt : σ → M) (m : M)
    (P : Polynomial (MvPolynomial σ R)) : Prop :=
  ∀ k, (P.coeff k).IsWeightedHomogeneous wt m

section CoeffHom

variable {σ M : Type*} [AddCommMonoid M] {wt : σ → M}

lemma CoeffHom.zero (m : M) : CoeffHom (R := R) wt m 0 := by
  intro k; rw [Polynomial.coeff_zero]; exact isWeightedHomogeneous_zero R wt m

lemma CoeffHom.mul {a b : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt a P)
    (hQ : CoeffHom wt b Q) : CoeffHom wt (a + b) (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (hP x.1).mul (hQ x.2))

lemma CoeffHom.C {m : M} {r : MvPolynomial σ R} (h : r.IsWeightedHomogeneous wt m) :
    CoeffHom wt m (Polynomial.C r) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact h
  · exact isWeightedHomogeneous_zero R wt m

lemma CoeffHom.X : CoeffHom (R := R) wt 0 Polynomial.X := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · exact isWeightedHomogeneous_one R wt
  · exact isWeightedHomogeneous_zero R wt 0

lemma CoeffHom.one : CoeffHom (R := R) wt 0 1 := by
  simpa using CoeffHom.C (R := R) (isWeightedHomogeneous_one R wt)

lemma CoeffHom.pow {a : M} {P : Polynomial (MvPolynomial σ R)} (h : CoeffHom wt a P) (e : ℕ) :
    CoeffHom wt (e • a) (P ^ e) := by
  induction e with
  | zero => simpa using CoeffHom.one (R := R) (wt := wt)
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul h

end CoeffHom

end ShearCoefficients

end Formalism.NormUnitaryCountingLemmas
