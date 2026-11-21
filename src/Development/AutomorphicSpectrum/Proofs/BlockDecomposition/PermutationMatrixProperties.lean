import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

namespace GlobalTheory.CompanionTheory.TyFin.Pm

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype K] [DecidableEq K] in

theorem glEquiv_apply {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) (i j : κ) :
    (glEquiv K e g : Matrix κ κ K) i j = (g : Matrix ι ι K) (e.symm i) (e.symm j) := rfl

end GlobalTheory.CompanionTheory.TyFin.Pm
