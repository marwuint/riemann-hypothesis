import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCard
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard : GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexTwo := by
  exact @GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex
