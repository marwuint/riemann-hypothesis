import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatake_weylInvariant : Formalism.UG.SatWeyl := by
  exact @GlobalTheory.SatakeWeyl.satWeyl
