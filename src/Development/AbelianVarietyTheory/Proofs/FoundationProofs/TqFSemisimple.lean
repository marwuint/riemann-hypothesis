import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspForms
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem tqF_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
  ∀ (f : CuspForm (Lev N l) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N l k hN hl hlN hk q σ hq hqNl hσ f c n hf
  obtain ⟨_, _, hT, hD, _⟩ := _root_.GlobalTheory.SlashUpperTriangularMatrices.bridge
  have hq0 : 0 < q := hq.pos
  have hfun : (fun F => TqF (k : ℤ) q σ F - c • F) = (fun h => GlobalTheory.Hk.heckeT (k:ℤ) q σ h - c • h) := by
    funext F; rw [hT _ _ _ _ hq0]
  have hσ' : GlobalTheory.Hk.IsDia N l ((q:ℕ):ℤ) σ := (hD N l q σ).1 (by simpa using hσ)
  rw [hfun] at hf
  rw [hT _ _ _ _ hq0]
  exact _root_.GlobalTheory.Hk.Semisimple.heckeT_semisimple N l q k σ c n (by omega) hl.pos hq hqNl hσ' f hf

end GlobalTheory.HeckeFamilyMatrices
