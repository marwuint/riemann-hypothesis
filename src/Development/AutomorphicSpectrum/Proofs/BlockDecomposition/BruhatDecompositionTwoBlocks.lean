import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import GroundTheory.AutomorphicForms.FiniteBruhat

open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.Bruhat

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

theorem pm_eq_permGL (σ : Equiv.Perm (Fin n)) : pm K σ = permGL K σ := rfl

end GlobalTheory.CompanionTheory.TyFin.Bruhat
