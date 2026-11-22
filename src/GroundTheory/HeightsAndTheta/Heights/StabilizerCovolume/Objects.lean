import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.TwistVecLinearIndependent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.LowerBoundFree.Line GroundTheory.Heights₂.Heights.NineStatements.Twist
open scoped Matrix

namespace LineFuller

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

def eBar : ⋀[Ω]^(2 - 1) ((Fin 2 → Ω) ⧸ lineF) := exteriorPower.ιMulti Ω (2 - 1) fun _ => lineF.mkQ (Pi.single 1 1)

end LineFuller

end GroundTheory.Heights₂.Heights.NineStatements
