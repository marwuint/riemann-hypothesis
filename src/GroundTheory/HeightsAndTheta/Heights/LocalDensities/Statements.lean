import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexOrder ContDiff

noncomputable section

def Across (N j' : ℕ) (i l : Fin N) : Prop := i.val < N - j' ∧ N - j' ≤ l.val

instance (N j' : ℕ) (i l : Fin N) : Decidable (Across N j' i l) := by
  unfold Across; infer_instance

def HermitianDetMono.Statement : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), B.PosSemidef → (A - B).PosSemidef →
    B.det.re ≤ A.det.re

end

end GroundTheory.Heights₂.Heights.FourB
