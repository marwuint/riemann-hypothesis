import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmOfGramEqSmul

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clm_of_gram_eq_smul' : ∀ {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E) (K : ℝ), (∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  exact @GlobalTheory.exists_clm_of_gram_eq_smul
