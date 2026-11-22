import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsFifthEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamifiedSumsFifthBound

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_gap_bound : _root_.GlobalTheory.BigTop.Fun.RankGapBound' := GlobalTheory.BigTop.Fun.rankGapBound_alt
end
