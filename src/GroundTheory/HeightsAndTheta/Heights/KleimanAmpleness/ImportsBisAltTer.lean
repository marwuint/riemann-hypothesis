import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver secOver secMOver)

def ReindexDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω) (N : ℕ)
    (e : κ ≃ Fin (N + 1)),
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => κ) F ⧸ mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) =
      ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (x' ∘ e.symm))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
