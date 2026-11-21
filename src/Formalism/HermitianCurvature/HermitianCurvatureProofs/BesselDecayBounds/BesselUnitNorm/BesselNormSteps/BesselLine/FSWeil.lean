import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section Weil

variable {k r : ℕ}

def psiMap (q : Mt k r × (Mt k r × Mt k r)) : Mt k r := fun i j => (sM q.2 * Matrix.of q.1) i j

theorem continuous_psiMap : Continuous (psiMap (k := k) (r := r)) := by
  have hc : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (sM q.2 * Matrix.of q.1 : Mx k r) :=
    ((PI.WUN.continuous_of.comp (continuous_fst.comp continuous_snd)).matrix_mul
      (PI.WUN.continuous_of.comp (continuous_snd.comp continuous_snd))).matrix_mul
      (PI.WUN.continuous_of.comp continuous_fst)
  exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem i j

theorem measurable_psiMap : Measurable (psiMap (k := k) (r := r)) := continuous_psiMap.measurable

theorem continuous_mulT : Continuous fun q : Mt k r × Mt k r => (fun i j => (Matrix.of q.2 * Matrix.of q.1) i j : Mt k r) := by
  have hc : Continuous fun q : Mt k r × Mt k r => (Matrix.of q.2 * Matrix.of q.1 : Mx k r) :=
    (PI.WUN.continuous_of.comp continuous_snd).matrix_mul (PI.WUN.continuous_of.comp continuous_fst)
  exact continuous_pi fun i => continuous_pi fun j => hc.matrix_elem i j

theorem muS_ne_zero {μG μS ν : Measure (Mt k r)} (hG0 : μG ≠ 0) (hq : IsQuotMeas μG μS ν) : μS ≠ 0 := by
  intro h0
  subst h0
  apply hG0
  have h1 := hq (fun _ => 1) measurable_const
  simpa using h1

theorem sfinite_quot {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS] (hG0 : μG ≠ 0)
    (hq : IsQuotMeas μG μS ν) : SFinite ν := by
  have hS0 := muS_ne_zero hG0 hq
  obtain ⟨f, hfpos, hfm, hfint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set F : Mt k r → ENNReal := fun x => (f x : ENNReal) with hFdef
  have hFm : Measurable F := hfm.coe_nnreal_ennreal
  have hmul : ∀ x : Mt k r, Measurable fun s : Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) :=
    fun x => (continuous_mulT.comp (Continuous.prodMk_right x)).measurable
  set h : Mt k r → ENNReal := fun x => ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS with hdef
  have hhm : Measurable h := (hFm.comp continuous_mulT.measurable).lintegral_prod_right'
  have hint : ∫⁻ x, h x ∂ν < ⊤ := by
    rw [hdef, ← hq F hFm]
    exact hfint.trans ENNReal.one_lt_top
  have hpos : ∀ x, h x ≠ 0 := by
    intro x hx
    have hx' := (lintegral_eq_zero_iff (hFm.comp (hmul x))).1 hx
    have hfalse : ∀ᵐ s ∂μS, False := hx'.mono fun s hs => by
      simp only [Function.comp_apply, Pi.zero_apply, hFdef, ENNReal.coe_eq_zero] at hs
      exact (hfpos _).ne' hs
    exact hS0 (by simpa using ae_iff.1 hfalse)
  have hfin : IsFiniteMeasure (ν.withDensity h) := isFiniteMeasure_withDensity hint.ne
  have heq : ν = (ν.withDensity h).withDensity h⁻¹ := by
    rw [← withDensity_mul ν hhm hhm.inv]
    conv_lhs => rw [← withDensity_one (μ := ν)]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_lt_top hhm hint.ne] with x hx
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact (ENNReal.mul_inv_cancel (hpos x) hx.ne).symm
  rw [heq]
  infer_instance

theorem quot_map {μG μW μN ν : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite ν]
    (hq : IsQuotMeas μG (muSof μW μN) ν) : μG = (ν.prod (μW.prod μN)).map psiMap := by
  ext A hA
  have hf : Measurable (A.indicator (1 : Mt k r → ENNReal)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA, hq _ hf,
    lintegral_map hf measurable_psiMap,
    lintegral_prod (fun w => A.indicator 1 (psiMap w)) (hf.comp measurable_psiMap).aemeasurable]
  refine lintegral_congr fun x => ?_
  have hf1 : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ENNReal)
      (fun i j => (Matrix.of s * Matrix.of x) i j) :=
    hf.comp (continuous_mulT.comp (Continuous.prodMk_right x)).measurable
  have hg1 : Measurable fun p : Mt k r × Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Mt k r) :=
    (continuous_mulT.comp continuous_swap).measurable
  rw [muSof, lintegral_map hf1 hg1]
  rfl

end Weil

end PI.WBL.FSW
