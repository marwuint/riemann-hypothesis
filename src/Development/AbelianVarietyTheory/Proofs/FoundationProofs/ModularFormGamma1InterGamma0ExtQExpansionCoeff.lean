import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansion
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem eq_of_coef_eq : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k,
    (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  intro N l k hN f g h
  ext τ
  have hf := _root_.GlobalTheory.Hk.lev_hasSum_coef N l k hN f τ
  have hg := _root_.GlobalTheory.Hk.lev_hasSum_coef N l k hN g τ
  simp_rw [h] at hf
  exact hf.unique hg

end GlobalTheory.Hk
