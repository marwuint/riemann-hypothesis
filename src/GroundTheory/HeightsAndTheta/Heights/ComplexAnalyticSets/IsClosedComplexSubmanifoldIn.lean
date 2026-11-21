import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Pointwise

variable {n d : ℕ}

def linPoly (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A (Pi.single j 1) i) * X j

def projAlgHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  aeval fun i => Ideal.Quotient.mk J (linPoly A i)

def IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) : Prop :=
  Function.Injective (projAlgHom J A) ∧ (projAlgHom J A).toRingHom.Finite

def unitaryRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {M | M * M.conjTranspose = 1}

def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    (∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
        (∃ M : Matrix (Fin d) (Fin n) ℂ, ∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) ∧
        ∀ M : Matrix (Fin d) (Fin n) ℂ,
          (∃ f ∈ S, eval (fun p => M p.1 p.2) f ≠ 0) → IsFiniteProjection J M.mulVecLin) ∧
      (∃ M : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J M.mulVecLin) ∧
      (∀ D ⊆ unitaryRows d n, unitaryRows d n ⊆ closure D →
        ∃ M ∈ D, IsFiniteProjection J M.mulVecLin) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) ℂ),
        (∀ k, F k ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((U * F k).conjTranspose.submatrix s id).mulVecLin))

def lineMap : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval ![X 0, 0]

def lineIdeal : Ideal (MvPolynomial (Fin 2) ℂ) := RingHom.ker lineMap

instance lineIdeal_isPrime : lineIdeal.IsPrime := RingHom.ker_isPrime _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
