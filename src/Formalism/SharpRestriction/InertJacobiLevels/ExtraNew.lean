import Formalism.LocalRingCardinality.DataExtra
import Formalism.SharpRestriction.InertJacobiLevels.ExtraZero
import Formalism.SharpRestriction.InertJacobiLevels.ExtraKer
import Formalism.LocalRingCardinality.DataNChoice

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped TensorProduct

instance trivialSide_ambient_subsingleton (D : D7) [Subsingleton D.what₂.EE0] (μ : D.what₂.Tup) : Subsingleton ((trivialSide D).s.Amb μ) :=
  inferInstanceAs (Subsingleton Examples₂.Z0)

end Formalism.MainNotions.Inhab

end
