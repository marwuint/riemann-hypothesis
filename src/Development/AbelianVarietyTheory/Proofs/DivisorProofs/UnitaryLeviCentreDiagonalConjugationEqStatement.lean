import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviCentreDiagonalConjugationEq
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq : GlobalTheory.SatakeWeyl.TorusConj := by
  exact @GlobalTheory.SatakeWeyl.TorusConjProof.torusConj
