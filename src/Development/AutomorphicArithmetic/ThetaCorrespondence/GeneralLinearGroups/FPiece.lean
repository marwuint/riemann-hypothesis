import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section SlopeTestRemainingChoices

open GlobalTheory.JacStages GlobalTheory.LocGL.SupportUnique

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private def Wd (W : ℕ → IrrGL k) (n : ℕ) (x : IrrGL k) : Prop :=
  ∃ hd : ∑ i : Fin n, (W i).1 = x.1, jm (fun i : Fin n => W i) hd x.rep ≠ 0

private def cut (W : ℕ → IrrGL k) (a b : ℕ) (j : Fin 2) (i : Fin (![a, b] j)) : IrrGL k :=
  W (finSigmaFinEquiv (n := ![a, b]) ⟨j, i⟩)

private theorem cut_one (W : ℕ → IrrGL k) (a b : ℕ) (i) : cut W a b 1 i = W (a + i) := by
  simp [cut, finSigmaFinEquiv_apply]

end SlopeTestRemainingChoices

