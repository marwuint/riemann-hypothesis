import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.EqOneOfUniLevi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NatSmulMulEq
import Mathlib

noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory MeasureTheory.Measure Topology Set NumberField
open scoped ENNReal NNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.AfT

theorem ofReal_smul {α : Type} [MeasurableSpace α] (x : ℝ) (μ : Measure α) :
    ENNReal.ofReal x • μ = x.toNNReal • μ := by
  rfl

end PI.IwaMeasEx.LP

end
