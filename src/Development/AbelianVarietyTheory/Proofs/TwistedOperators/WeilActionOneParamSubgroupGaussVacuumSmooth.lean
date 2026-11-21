import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanLineOperatorsOneParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLineTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquationsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracePairingArchimedeanVarsNondegenerateRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothly

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.GaussLine

theorem smooth_vacuum_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) → ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := _root_.GlobalTheory.LineGroup.archOp_oneParam B G X om om' hT γ hγ T hTa
  have hU := _root_.GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq B G X om om' hT γ hγ T hTa Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := _root_.GlobalTheory.ArchLineAct.intertwine B G X om om' hT γ hγ T hTa
  have hC := _root_.GlobalTheory.ArchLineCont.continuous_apply B G X om om' hT γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := GlobalTheory.T.exists_complexStructure_gaussVacuum_fockEquations B G X om om' hT f₀ hf₀
  haveI : BorelSpace (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, n, qs, qs', cs, c, hd⟩ := _root_.GlobalTheory.WeilVacuum.smooth_flow (V := Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')))
    (_root_.GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ G.M.Pol B.ψ B.emb := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := _root_.GlobalTheory.PolMul.pol_mul_pairInf B G X om om' hT
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.GaussLine
