import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FSLevi

variable {J : Type} [Fintype J]

def reP (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj p)

def imaginary (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj p)

def nsq (z : J → ℂ) : ℝ := ∑ p, (reP p z ^ 2 + imaginary p z ^ 2)

theorem reP_apply (p : J) (z : J → ℂ) : reP p z = (z p).re := rfl

theorem imaginaryPart_apply (p : J) (z : J → ℂ) : imaginary p z = (z p).im := rfl

theorem norm_sq_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem nsq_pos {z : J → ℂ} (hz : z ≠ 0) : 0 < nsq z := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hz
  refine Finset.sum_pos' (fun q _ ↦ by positivity) ⟨p, Finset.mem_univ _, ?_⟩
  rw [reP_apply, imaginaryPart_apply, ← norm_sq_eq]
  exact pow_pos (norm_pos_iff.mpr hp) 2

end FSLevi

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
