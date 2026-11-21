import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
import GroundTheory.AutomorphicForms.CuspidalSplittingIsotypic
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocR
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsCovByRelJacD
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FCount
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FProdStart
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

open GlobalTheory.Parabolic (Embeds)
open GlobalTheory.ProdFlatten

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private def EB {n : ℕ} (A C : BR k n) : Prop := Embeds A.ρ C.ρ

private theorem EB.trans {n : ℕ} {A C D : BR k n} (h : EB A C) (h' : EB C D) : EB A D := Embeds.trans h h'

unseal GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in
private theorem EB_pr {p q N : ℕ} {x : Fin p → IrrGL k} {y : Fin q → IrrGL k} (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : EB (pr x hx) (pr y hy) ↔ Embeds (prodIrr x hx) (prodIrr y hy) := Iff.rfl

attribute [irreducible] EB

private def PE {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) : Prop :=
  ∑ a, (x a).1 = ∑ a, (y a).1 ∧
    ∀ (N : ℕ) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N), EB (pr x hx) (pr y hy)

private theorem PE.trans {p q r : ℕ} {x : Fin p → IrrGL k} {y : Fin q → IrrGL k} {z : Fin r → IrrGL k}
    (h : PE x y) (h' : PE y z) : PE x z :=
  ⟨h.1.trans h'.1, fun N hx hz => (h.2 N hx (h.1.symm.trans hx)).trans (h'.2 N _ hz)⟩

private theorem exists_cls {c : ℕ} (w : Fin c → IrrGL k) (hi : (prodIrr w rfl).IsIrreducible) :
    ∃ (x : IrrGL k) (hd : ∑ a, (w a).1 = x.1), Embeds (prodIrr w hd) x.rep ∧ IsSubquotient x.rep (prodIrr w hd) := by
  have φ := IrrGL.equivOf (prodIrr w rfl) (isSmooth_prodIrr w rfl) hi
  exact ⟨IrrGL.of (prodIrr w rfl) (isSmooth_prodIrr w rfl) hi, rfl, .of_equiv φ,
    .of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective⟩

end

