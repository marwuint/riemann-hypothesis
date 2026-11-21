import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import GroundTheory.AutomorphicForms.ReductionSplitting
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HenQ.DetDParts

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem top_add_one_le : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := le_of_eq rfl

theorem fderiv_fderiv_comm {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ g y u) x v = fderiv ℝ (fun y => fderiv ℝ g y v) x u := by
  have hgx : ContDiffAt ℝ (⊤ : ℕ∞) g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgx.fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero
  have key : ∀ a b : E, fderiv ℝ (fun y => fderiv ℝ g y a) x b = fderiv ℝ (fderiv ℝ g) x b a := by
    intro a b
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  rw [key, key]
  exact (hgx.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)).eq v u

variable {μ : Measure E} [μ.IsAddHaarMeasure]

theorem continuous_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hs : tsupport χ ⊆ U) :
    Continuous fun x => χ x * u x :=
  (hχ.continuousOn.mul hu).continuous_of_tsupport_subset hU (tsupport_mul_subset_left.trans hs)

theorem integrable_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
    Integrable (fun x => χ x * u x) μ :=
  (continuous_mul_of_tsupport hU hu hχ hs).integrable_of_hasCompactSupport hc.mul_right

theorem integral_partial_mul {U : Set E} (hU : IsOpen U) {Ψ g : E → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hc : HasCompactSupport Ψ) (hs : tsupport Ψ ⊆ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (u : E) :
    ∫ x, fderiv ℝ Ψ x u * g x ∂μ = -∫ x, Ψ x * fderiv ℝ g x u ∂μ := by
  have h1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hg1 : ContDiffOn ℝ 1 g U := hg.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffOn ℝ 0 (fun x => fderiv ℝ g x u) U :=
    (hg1.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  rw [eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_tsupport hU hg1.continuousOn
      ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hs))
    (integrable_mul_of_tsupport hU hg'.continuousOn h1.continuous hc hs)
    (integrable_mul_of_tsupport hU hg1.continuousOn h1.continuous hc hs)
    (fun x _ => h1.differentiable one_ne_zero x)
    (fun x hx => (hg1.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)

end General

end GlobalTheory.HenQ.DetDParts
