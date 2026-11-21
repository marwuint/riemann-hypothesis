import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibre
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapArea

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)

open scoped ENNReal

theorem gramVol_congr {e n : ℕ} {v v' : (Fin e → ℂ) → (Fin n → ℂ)} {y : Fin e → ℂ}
    (h : v =ᶠ[𝓝 y] v') : gramVol v y = gramVol v' y := by
  unfold gramVol
  rw [h.eq_of_nhds, h.fderiv_eq]

def gramForm {e n : ℕ} (p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ))) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons p.1 fun j => p.2 (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

theorem gramVol_eq_gramForm {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y = gramForm (v y, fderiv ℂ v y) := rfl

theorem continuous_gramForm {e n : ℕ} :
    Continuous (gramForm : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) → ℝ) := by
  have hw : Continuous fun p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) =>
      (Fin.cons p.1 fun j => p.2 (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) := by
    refine continuous_pi fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa using continuous_fst
    · simpa using continuous_snd.clm_apply continuous_const
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp ((continuous_apply a).comp hw)).star.mul
    ((continuous_apply i).comp ((continuous_apply b).comp hw))

theorem aemeasurable_coneTerm {e n : ℕ} {U D : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hU : IsOpen U) (hDU : D ⊆ U)
    (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (fun x => ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)) (volume.restrict D) := by
  have ha : AEMeasurable v (volume.restrict D) :=
    (hv.continuousOn.aemeasurable hU.measurableSet).mono_measure (Measure.restrict_mono hDU le_rfl)
  have hg : AEMeasurable (fun x => gramVol v x) (volume.restrict D) := by
    have h := continuous_gramForm.measurable.comp_aemeasurable
      (ha.prodMk (measurable_fderiv ℂ v).aemeasurable)
    simpa only [Function.comp_def, ← gramVol_eq_gramForm] using h
  have hmeas : Measurable fun p : (Fin e → ℂ) × ℂ => F (p.2 • WithLp.toLp 2 (ha.mk v p.1)) *
      ENNReal.ofReal (‖p.2‖ ^ (2 * e) * hg.mk _ p.1) := by
    refine (hF.comp (measurable_snd.smul ((PiLp.continuous_toLp 2 _).measurable.comp
      (ha.measurable_mk.comp measurable_fst)))).mul ?_
    exact ENNReal.measurable_ofReal.comp
      ((measurable_snd.norm.pow_const _).mul (hg.measurable_mk.comp measurable_fst))
  refine ⟨_, hmeas.lintegral_prod_right' (ν := (volume : Measure ℂ)), ?_⟩
  filter_upwards [ha.ae_eq_mk, hg.ae_eq_mk] with x h1 h2
  simp only [h1, h2]

end GroundTheory.Heights₂.Heights
