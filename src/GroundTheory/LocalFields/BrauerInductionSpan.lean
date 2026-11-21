import Mathlib
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.LocalFields.BrauerInductionElementary

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

variable {G : Type*} [Group G] [Fintype G]

def indLin (K : Subgroup G) (l : K →* ℂˣ) : G → ℂ := indFun K.subtype (fun k ↦ (l k : ℂ))

end GroundTheory.LocalField
