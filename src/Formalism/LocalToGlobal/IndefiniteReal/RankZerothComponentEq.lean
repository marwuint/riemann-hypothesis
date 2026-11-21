import Mathlib
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.ZuckDualOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualDefs
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.ConjRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
import Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.SharpRestriction.Divisibility.FunctionModelRallisFromInputs
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult

namespace Formalism.IndefR.ModelConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lamS_eq (R : Ranks) (P : HCParam R) (i : Fin R.r) : Formalism.MainNotions.S.lamS R P i = ((lamAt P i : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS lamAt
  split_ifs <;> simp

variable {D : D7}

variable {S : D.what₂.Tau → SPar}

end Formalism.IndefR.ModelConjugation
