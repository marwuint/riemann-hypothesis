import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def sharp (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : E[X] :=
  C (c (P.coeff 0))⁻¹ * reflect r (P.map (c : E →+* E))

def IsPPol (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P.natDegree = r ∧ P.coeff 0 ≠ 0 ∧ P = sharp c r P

variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}

theorem isUnit_root (hP : IsPPol c r P) : IsUnit (AdjoinRoot.root P) := by
  haveI : Fact (Irreducible P) := ⟨hP.2.1⟩
  refine Ne.isUnit fun h => hP.2.2.2.1 ?_
  have h1 := AdjoinRoot.eval₂_root P
  rw [h, eval₂_at_zero] at h1
  exact (map_eq_zero_iff _ (AdjoinRoot.of P).injective).1 h1

def alpha (hP : IsPPol c r P) : (AdjoinRoot P)ˣ := (isUnit_root hP).unit

theorem alpha_val (hP : IsPPol c r P) : (alpha hP : AdjoinRoot P) = AdjoinRoot.root P := rfl

variable (k : Type) [Field k] [Algebra F k]

@[reducible] def algLk (P : E[X]) : Algebra (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F E (AdjoinRoot P))
    (AlgHom.id F k)).toRingHom.toAlgebra

attribute [local instance] algLk

variable {k}

variable (k)

end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
