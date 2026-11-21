import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

open GlobalTheory.CompanionTheory.PairMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_multiplicity_top_cycle : GlobalTheory.CompanionTheory.PairMult.TopCyc := by
  exact @GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc
