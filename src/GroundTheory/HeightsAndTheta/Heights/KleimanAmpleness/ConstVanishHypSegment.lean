import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell faceSign)

open Classical in

def constD (K : Type*) [Fintype K] [LinearOrder K] (ι : K → Type*) [∀ k, LinearOrder (ι k)] (V : Type*)
    [AddCommGroup V] (n : ℕ) (f : Cell K ι n → V) : Cell K ι (n + 1) → V :=
  fun I => ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      faceSign I.1 k i • f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
