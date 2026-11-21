import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffAdjacentSwapOfLeviReduction
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction : GlobalTheory.SatakeWeyl.LeviStep → GlobalTheory.SatakeWeyl.IndexFour → GlobalTheory.SatakeWeyl.CartanFour → GlobalTheory.SatakeWeyl.CoeffSwap := by
  exact @GlobalTheory.SatakeWeyl.Swap.coeffSwap
