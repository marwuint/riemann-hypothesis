import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupFiltration

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing GroundTheory.LocalField.FormalGroup

section FormalGroupPoints

variable {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

namespace MaxIdealPoint

variable {F G H : FormalGroup 𝒪}

end MaxIdealPoint

end FormalGroupPoints

end

end GroundTheory.Arith.Abelian
