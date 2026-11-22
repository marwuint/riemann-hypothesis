import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormTwelveCubedEqOneOfFiveLePrime

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy jInv)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.InvariantFactorPaths.G7 (at1)

namespace ThetaHomothety

open Formalism.L2.Th1.F (scalePair opU herm th0 area taylor0 sgStar)

theorem herm_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z x : ℂ) :
    herm (scalePair L c hc) (c * z) (c * x) = herm L z x := by
  exact Formalism.L2.Th1.F.Homog.herm_scale (L := L) (c := c) (hc := hc) z x

theorem opU_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ s z : ℂ) :
    opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)) (c * z) =
      opU L s (th0 L (ω₀ / 2)) z := by
  unfold opU
  rw [herm_scale L c hc z s, herm_scale L c hc s s]
  have h1 : c * ω₀ / 2 = c * (ω₀ / 2) := by ring
  have h2 : c * z + c * s = c * (z + s) := by ring
  rw [h1, h2, Formalism.L2.Th1.F.Homog.normalizedTheta_scale (L := L) (c := c) (hc := hc)]

theorem differentiable_opU (L : PeriodPair) (s : ℂ) {θ : ℂ → ℂ} (h : Differentiable ℂ θ) :
    Differentiable ℂ (opU L s θ) := by
  show Differentiable ℂ fun z =>
    θ (z + s) * Complex.exp (-(Real.pi : ℂ) * herm L z s - (Real.pi : ℂ) * herm L s s / 2)
  simp only [herm]
  fun_prop

theorem differentiable_evenTheta (L : PeriodPair) (t : ℂ) : Differentiable ℂ (th0 L t) := by
  have hs : Differentiable ℂ (sgStar L) := (Formalism.L2.Th1.F.sgStarBasic L).1
  show Differentiable ℂ fun z => opU L t (sgStar L) z / opU L t (sgStar L) 0
  exact (differentiable_opU L t hs).div_const _

theorem taylor0_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ s : ℂ) :
    PowerSeries.rescale c
        (taylor0 (opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)))) =
      taylor0 (opU L s (th0 L (ω₀ / 2))) := by
  have hd : Differentiable ℂ
      (opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2))) :=
    differentiable_opU _ _ (differentiable_evenTheta _ _)
  have hF : (fun z => opU (scalePair L c hc) (c * s) (th0 (scalePair L c hc) (c * ω₀ / 2)) (c * z)) =
      opU L s (th0 L (ω₀ / 2)) := funext (opU_scale L c hc ω₀ s)
  ext n
  simp only [taylor0, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  rw [← hF, iteratedDeriv_comp_const_mul hd.contDiff c]
  simp only [mul_zero]
  ring

end ThetaHomothety

end Formalism.L2.Th1.Top
