import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocks
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSimpleAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowToColumnReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalParametrization

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem isIrr_of_simple (τ : FDRep ℂ Γ) [h : Simple τ] : IsIrr τ.ρ := (_root_.GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 Γ τ).1 h

theorem zIdemIdemCentral_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (hτ : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := _root_.GlobalTheory.CompanionTheory.TyFin.zIdemFacts.1 Γ τ hτ

theorem zIdemOrthogonal_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ)
    (h : ¬ Nonempty (τ ≅ σ)) : zIdem τ * zIdem σ = 0 := _root_.GlobalTheory.CompanionTheory.TyFin.zIdemFacts.2.1 Γ τ σ hτ hσ h

end Gen

section GeneralLinearIntegers

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem CuspIso.symm {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} (h : CuspIso K lam mu) : CuspIso K mu lam :=
  (_root_.GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β β lam lam mu mu (Equiv.refl α |>.trans (Classical.choose h))).1 h

theorem CuspIso.trans {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} {nu : FDRep ℂ (GL γ K)}
    (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu :=
  (_root_.GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts K α β γ lam lam mu nu (Classical.choose h)).2.1 h h'

end GeneralLinearIntegers

end ReciprocityTheory.Ty.Fin
