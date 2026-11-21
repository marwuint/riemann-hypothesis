import Formalism.CyclotomicNorms.StatementTW

open Polynomial Matrix

namespace Formalism.CyclotomicNorms
noncomputable section

namespace residueMatrixData

section SNF
variable {R : Type*} [CommRing R]

def ext1 {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : Matrix (Fin (a+1)) (Fin (a+1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => P i' j') j) i

@[simp] lemma blockExtend_zero_zero {a : ℕ} (P : Matrix (Fin a) (Fin a) R) : ext1 P 0 0 = 1 := rfl
@[simp] lemma blockExtend_zero_succ {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (j : Fin a) : ext1 P 0 j.succ = 0 := rfl
@[simp] lemma blockExtend_succ_zero {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (i : Fin a) : ext1 P i.succ 0 = 0 := rfl
@[simp] lemma blockExtend_succ_succ {a : ℕ} (P : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    ext1 P i.succ j.succ = P i j := rfl

end SNF

section Trunc
variable {K' : Type} [Field K'] {n : ℕ}

local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)

def pbT (K' : Type) [Field K'] (n : ℕ) : PowerBasis K' (TruncK K' n) :=
  AdjoinRoot.powerBasis' (monic_X_pow n)

instance (K' : Type) [Field K'] (n : ℕ) : FiniteDimensional K' (TruncK K' n) := (pbT K' n).finite

end Trunc

section Mod
variable {K' : Type} [Field K'] {n : ℕ}

local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)

instance finite_sub {a : ℕ} (p : Submodule (TruncK K' n) (Fin a → TruncK K' n)) :
    Module.Finite K' ↥p :=
  Module.Finite.of_injective (p.subtype.restrictScalars K') Subtype.val_injective

end Mod

end residueMatrixData

end
end Formalism.CyclotomicNorms
