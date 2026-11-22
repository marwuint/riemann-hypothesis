import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.CoinvExact

section Coinv

variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}

end Coinv

end GlobalTheory.CompanionTheory.CoinvExact
