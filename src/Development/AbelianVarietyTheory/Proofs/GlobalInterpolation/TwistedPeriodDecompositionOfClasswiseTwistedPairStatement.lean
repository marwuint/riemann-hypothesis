import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPair
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPeriodDecomposition_of_classwiseTwistedPairingIntegral : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  exact @GlobalTheory.PerRedTw.reduction_perDecTw
