import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints

noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.NGDict

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.MainNotions.BridgeLemma Formalism.MainNotions.KappaEndpoints

section Steps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

def StepHp (P : FPair H r) : Prop := (qF F : ℝ) ≤ P.Hp

end Steps

end Formalism.L2.SG.NGDict
