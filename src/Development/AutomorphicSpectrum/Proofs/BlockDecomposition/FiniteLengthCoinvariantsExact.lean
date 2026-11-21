import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.CoinvExact

section Coinv

variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}

theorem twRel_le_comap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ).comap φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, v, rfl⟩
  refine Submodule.subset_span ⟨γ, φ v, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]

def coinvMap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    (coinv τ₁ ψ).IntertwiningMap (coinv τ₂ ψ) where
  toLinearMap := Submodule.mapQ _ _ φ.toLinearMap (twRel_le_comap φ ψ)
  isIntertwining' := fun g => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    exact congrArg (Submodule.Quotient.mk (p := twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ))
      (φ.isIntertwining _ _ (1, g) v)

theorem coinvMap_mk (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) (v : V₁) :
    coinvMap φ ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := rfl

end Coinv

end GlobalTheory.CompanionTheory.CoinvExact
