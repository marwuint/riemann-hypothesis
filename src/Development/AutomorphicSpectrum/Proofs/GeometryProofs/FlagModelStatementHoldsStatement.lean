import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHolds
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlagModelStatement

open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FlagModelStatement_holds : FlagModelStatement := by
  exact @GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel
