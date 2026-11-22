import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticLegendre
import GroundTheory.GlobalFields.Artin.ConductorInduction
import GroundTheory.GlobalFields.Artin.ConductorOneDim

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Module GroundTheory.LocalField NumberField.InfinitePlace NumberField.Units
open scoped Real

namespace GroundTheory.Global

namespace Quadratic

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

instance : NeZero (discr K).natAbs :=
  ⟨Int.natAbs_ne_zero.2 (discr_ne_zero K)⟩

end Quadratic

end GroundTheory.Global
