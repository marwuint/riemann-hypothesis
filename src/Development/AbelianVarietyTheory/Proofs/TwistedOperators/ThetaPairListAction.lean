import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumLineFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open Filter Topology

noncomputable section
open scoped Classical

namespace GlobalTheory.LineAdd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem tens_add_smul (f s : SInf F κ) (t : ℝ) (r : (κ → AF F) → ℂ) :
    tens (evI F) ⇑(f + t • s) r = tens (evI F) ⇑f r + (t : ℂ) • tens (evI F) ⇑s r := by
  funext x
  simp only [tens, SchwartzMap.add_apply, SchwartzMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

theorem hasDerivAt_of_curve {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f g : SInf F κ} {c : ℝ → SInf F κ}
    {r : (κ → AF F) → ℂ} (hc : ∀ t, T t (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) (hc0 : c 0 = f)
    (hlim : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 g)) :
    ∀ x, HasDerivAt (fun t => T t (tens (evI F) ⇑f r) x) (tens (evI F) ⇑g r x) 0 := by
  intro x
  have ev : ∀ y : κ → mixedEmbedding.mixedSpace F, Continuous fun s : SInf F κ => s y := by
    intro y
    have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous
    exact (continuous_eval_const (F := BoundedContinuousFunction (κ → mixedEmbedding.mixedSpace F) ℂ) y).comp h1
  have e : (fun t => T t (tens (evI F) ⇑f r) x) = fun t => tens (evI F) ⇑(c t) r x := by
    funext t; rw [hc t]
  rw [e, hasDerivAt_iff_tendsto_slope]
  refine ((((ev _).tendsto g).comp hlim).mul_const (r x)).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, tens]
  rw [slope_def_module, hc0]
  simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul, smul_eq_mul]
  ring

end

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

theorem om_prod_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (a b : UA σ Y.J) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om (a * b, 1) Φ = om (a, 1) (om (b, 1) Φ) := by
  have e : ((a * b, (1 : UA σ Wd.J)) : UA σ Y.J × UA σ Wd.J) = (a, 1) * (b, 1) := by
    simp [Prod.mk_mul_mk]
  rw [e, map_mul, Module.End.mul_apply]

theorem om_one_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om ((1 : UA σ Y.J), (1 : UA σ Wd.J)) Φ = Φ := by
  rw [show ((1 : UA σ Y.J), (1 : UA σ Wd.J)) = (1 : UA σ Y.J × UA σ Wd.J) from rfl, map_one, Module.End.one_apply]

end GlobalTheory.LineAdd

