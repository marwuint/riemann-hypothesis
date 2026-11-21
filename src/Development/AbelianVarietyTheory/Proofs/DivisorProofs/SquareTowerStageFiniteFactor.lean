import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun
import Development.AutomorphicArithmetic.DivisorFrames.IsSBHalfThetaFunOfHalfIdempotentPlaces
import Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdFstEqProductLocal
import Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdSndEqProductLocal
import Development.AutomorphicArithmetic.DivisorFrames.BigPStdSchwartzTranslateEqSmallPOfIsUnif
import Development.AutomorphicArithmetic.DivisorFrames.ExistsPolynomialOfIsFinFThetaLiftPureTensor
import Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
import Development.AutomorphicArithmetic.DivisorFrames.StdAStdBMemSchwartzBruhat
import Development.AutomorphicArithmetic.DivisorFrames.ExistsLatticeThetaDataOfRamificationPlacesCMDatu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGrids
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFinitePlacesUnramifiedOrSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilUnramifiedFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryFramesSignatures

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.StageFinMatch

theorem gBig_two' {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

theorem tmul_right_prop {K V U : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {a a' : V} {b b' : U} (h : a ⊗ₜ[K] b = a' ⊗ₜ[K] b') (hne : a ⊗ₜ[K] b ≠ 0) : ∃ μ : K, μ ≠ 0 ∧ b = μ • b' := by
  have ha : a ≠ 0 := by rintro rfl; exact hne (TensorProduct.zero_tmul _ _)
  have hb : b ≠ 0 := by rintro rfl; exact hne (TensorProduct.tmul_zero _ _)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ha ((Module.forall_dual_apply_eq_zero_iff K a).mp hc)
  have k := congrArg (fun z => TensorProduct.lid K U (LinearMap.rTensor U φ z)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at k
  have hb' : b = (φ a' / φ a) • b' := by
    rw [div_eq_inv_mul, mul_smul, ← k, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  refine ⟨φ a' / φ a, ?_, hb'⟩
  intro h0
  rw [h0, zero_smul] at hb'
  exact hb hb'

end GlobalTheory.StageFinMatch

namespace GlobalTheory.StageFinMatch

end GlobalTheory.StageFinMatch
