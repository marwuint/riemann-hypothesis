import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicit
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeUOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.uOp q f τ) := by
  exact @GlobalTheory.Hk.hasSum_uOp
