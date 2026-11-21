import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_total : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  exact @GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal
