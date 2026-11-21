import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime IsMultiHomog IsRelevant geoNum)

def ChowDegreeGeoNum.Statement : Prop :=
  ∀ (n e p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      ringKrullDim (MRing (PBlk n) ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞) →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        (chowDegree ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F))) (e + 1)
          : ℤ) = geoNum e W (fun _ _ => 1)

end ObjectsChow

end GroundTheory.Heights₂.Heights
