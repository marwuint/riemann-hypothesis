import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

abbrev ι0 : Empty → Type := fun k => k.elim

instance instFintypeι0 : ∀ k : Empty, Fintype (ι0 k) := fun k => k.elim

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
