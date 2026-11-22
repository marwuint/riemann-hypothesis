import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.BotReading
import Development.AutomorphicArithmetic.LocalEmbeddings.BotPair
import Development.AutomorphicArithmetic.LocalEmbeddings.BotLocal
import Development.AutomorphicArithmetic.DivisorFrames.ThetaTransformFockModelEqOfStandardChar
import Development.AutomorphicArithmetic.DivisorFrames.StdSectionFirstEqProdLocal
import Development.AutomorphicArithmetic.DivisorFrames.StdSectionSecondEqProdLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilUnramifiedFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFinRef

theorem exists_dual_eq_one {M : Type} [AddCommGroup M] [Module ℂ M] {a : M} (ha : a ≠ 0) :
    ∃ φ : M →ₗ[ℂ] ℂ, φ a = 1 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ M, φ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha ((Module.forall_dual_apply_eq_zero_iff ℂ a).1 h)
  exact ⟨(φ a)⁻¹ • φ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]⟩

theorem contract_tmul {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (φ : M →ₗ[ℂ] ℂ)
    (a : M) (b : N) : (TensorProduct.lid ℂ N) (φ.rTensor N (a ⊗ₜ b)) = φ a • b := by
  simp

theorem exists_smul_of_tmul_eq {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {a c : M}
    {b d : N} (ha : a ≠ 0) (h : a ⊗ₜ[ℂ] b = c ⊗ₜ[ℂ] d) : ∃ l : ℂ, b = l • d := by
  obtain ⟨φ, hφ⟩ := exists_dual_eq_one ha
  refine ⟨φ c, ?_⟩
  have := congrArg (fun z => (TensorProduct.lid ℂ N) (φ.rTensor N z)) h
  simp only [contract_tmul, hφ, one_smul] at this
  exact this

theorem tensor_eq_zero_of_subsingleton {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    [Subsingleton M] (z : M ⊗[ℂ] N) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem exists_smul_of_factor {Q Q' Pr Pf Pi : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q']
    [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi]
    (q : Q →ₗ[ℂ] Pr) (q' : Q' →ₗ[ℂ] Pr) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) (hq : Function.Surjective q) (x x' : Pf)
    (a : Q → Pi) (a' : Q' → Pi) (ha : ∀ P, a P = e (q P ⊗ₜ x)) (ha' : ∀ P', a' P' = e (q' P' ⊗ₜ x'))
    (H : (∀ P, a P = 0) ∨ ∃ (P : Q) (P' : Q') (κ : ℂ), a P ≠ 0 ∧ a P = κ • a' P') : ∃ κ : ℂ, x = κ • x' := by
  rcases H with H | ⟨P, P', κ, h0, h1⟩
  ·
    have hPr : Nontrivial Pr := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      obtain ⟨z, hz⟩ := exists_ne (0 : Pi)
      refine hz ?_
      rw [← e.apply_symm_apply z, tensor_eq_zero_of_subsingleton (e.symm z), map_zero]
    obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
    obtain ⟨P, rfl⟩ := hq y
    have h2 : q P ⊗ₜ[ℂ] x = q P ⊗ₜ[ℂ] (0 : Pf) := by
      rw [TensorProduct.tmul_zero]
      apply e.injective
      rw [← ha, H, map_zero]
    obtain ⟨l, hl⟩ := exists_smul_of_tmul_eq hy h2
    exact ⟨0, by rw [hl, smul_zero, zero_smul]⟩
  · have h2 : q P ⊗ₜ[ℂ] x = q' P' ⊗ₜ[ℂ] (κ • x') := by
      apply e.injective
      rw [← ha, h1, ha', ← LinearEquiv.map_smul, TensorProduct.tmul_smul]
    have hy : q P ≠ 0 := by
      intro h
      exact h0 (by rw [ha, h, TensorProduct.zero_tmul, map_zero])
    obtain ⟨l, hl⟩ := exists_smul_of_tmul_eq hy h2
    exact ⟨l * κ, by rw [hl, smul_smul]⟩

theorem gBig_mono {Q₁ Q₂ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₂ := by
  obtain ⟨a₁, h₁⟩ := h₁
  refine ⟨a₁, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF hCF
  exact ⟨C₁, x₁, fun C hC D large₂ he hx r T Lc μ hLc G => H G μ C _ _ (h₁ C hC D large₂ he hx r T Lc μ hLc G)⟩

end GlobalTheory.BotFinRef

namespace GlobalTheory.BotFinRef

end GlobalTheory.BotFinRef
