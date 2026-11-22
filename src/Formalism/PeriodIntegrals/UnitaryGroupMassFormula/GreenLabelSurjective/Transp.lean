import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.GreenLabelSurjWork

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem glEquiv_val (e : ι ≃ κ) (g : GL ι K) :
    ((glEquiv K e g : GL κ K) : Matrix κ κ K) = Matrix.reindex e e (g : Matrix ι ι K) := rfl

theorem transp_ρ (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (g : GL κ K) :
    (transp e τ).ρ g = τ.ρ ((glEquiv K e).symm g) := rfl

end PI.GreenLabelSurjWork
