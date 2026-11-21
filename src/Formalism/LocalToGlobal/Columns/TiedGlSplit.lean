import Formalism.LocalToGlobal.Columns.TiedGlPl
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

include hc in

theorem gls_trace_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a + cO E a := by
  obtain ⟨b0, hb0⟩ := rll_norm_mem hc a
  obtain ⟨b1, hb1⟩ := rll_norm_mem hc (a + 1)
  refine ⟨b1 - b0 - 1, ?_⟩
  rw [map_sub, map_sub, map_one, hb1, hb0, map_add (cO E), map_one]
  ring

end Tr

end Formalism.L2.Col
