import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal
