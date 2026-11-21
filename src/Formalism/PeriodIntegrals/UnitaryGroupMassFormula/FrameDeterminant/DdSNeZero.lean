import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.FrameB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DetOfFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem

noncomputable section

open NumberField

namespace PI.TripleFrameDeterminant.W

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.IsoDetDefs PI.FlagFrameDeterminants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 :=
  PI.ScalarPairDr.W.ddS_ne_zero D

end PI.TripleFrameDeterminant.W
