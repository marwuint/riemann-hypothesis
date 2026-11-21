import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.TraceIndexFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_index_formula : TraceIndex := by
  exact @GlobalTheory.CompanionTheory.InertZeta.traceIndex
