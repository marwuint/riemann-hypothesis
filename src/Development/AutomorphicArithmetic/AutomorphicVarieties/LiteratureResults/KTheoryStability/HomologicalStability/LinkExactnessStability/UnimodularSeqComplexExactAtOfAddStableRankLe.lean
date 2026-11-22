import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtUnimodularSeqsOfAddStableRankLe
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.unimodularSeqComplex_exactAt_of_add_stableRank_le : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ m q : ℕ, q + s ≤ m → ExactAt (uniSeq R m) q := GlobalTheory.uniSeq_exactAt_of_stableRangeLe
end
