import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumHilbertSum

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)

def CuspDiscrete : Prop :=
  ∀ π : CuspSub E N, π.IsUnitary → IsNormalised π → IsDiscrete π.V

end PositivityTheory.RSHS

end
