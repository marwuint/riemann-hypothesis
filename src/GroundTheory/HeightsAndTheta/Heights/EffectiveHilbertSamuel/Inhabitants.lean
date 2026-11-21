import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Objects
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def flatAtlas (D : ℕ) : FinHolAtlas D (Fin D → ℂ) where
  n := 1
  chart _ := OpenPartialHomeomorph.refl _
  cover _ := ⟨0, by simp⟩
  holo _ _ := by
    intro x _
    simpa [Function.comp_def] using analyticAt_id

instance (D : ℕ) : Subsingleton (Fin (flatAtlas D).n) := inferInstanceAs (Subsingleton (Fin 1))

@[simp] theorem flatAtlas_chart (D : ℕ) (j : Fin (flatAtlas D).n) :
    (flatAtlas D).chart j = OpenPartialHomeomorph.refl _ := rfl

end

end GroundTheory.Heights₂.Heights.EffectiveHS
