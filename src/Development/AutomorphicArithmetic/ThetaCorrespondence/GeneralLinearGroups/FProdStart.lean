import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfClsGLEqSingle
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompL
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FCount

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

open GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem prod_X_monomial {σ : Type*} {h : ℕ} (Δ : Fin h → σ) (f : Fin h → MvPolynomial σ ℤ)
    (hf : ∀ i, f i = MvPolynomial.X (Δ i)) : ∃ m, ∏ i, f i = MvPolynomial.monomial m (1 : ℤ) := by
  refine Finset.prod_induction _ (fun p => ∃ m, p = MvPolynomial.monomial m (1 : ℤ)) ?_ ⟨0, rfl⟩ fun i _ => ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [MvPolynomial.monomial_mul, one_mul]⟩
  · exact ⟨_, hf i⟩

end

