import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable locDens)

noncomputable section

def shellConst (D : ℕ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) ^ (D + 1) / 2 ^ k

def TailLogOfMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Yo : Set X) (r : X → ℝ) (th : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → ContinuousOn r Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → IsPotential A th → (∀ i, A.SmoothOn Yo (u i)) →
    (∀ i, FormNonneg A Yo (potForm th (u i))) → ∀ CE : ℝ,
    TailMassBound A Yo r (fun i => potForm th (u i)) CE →
    TailLogBound A Yo r (fun i => potForm th (u i)) (shellConst D * CE)

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
