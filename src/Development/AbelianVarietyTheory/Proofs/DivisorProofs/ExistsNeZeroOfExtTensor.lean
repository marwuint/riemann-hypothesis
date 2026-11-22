import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ReducedFactor

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_irr {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [Subsingleton.elim x 0]
  exact iff_of_true (zero_mem _) (zero_mem _)

end General

end GlobalTheory.ReducedFactor

namespace GlobalTheory.ReducedFactor

end GlobalTheory.ReducedFactor
