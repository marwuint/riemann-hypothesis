import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.correctionSt_of_transportSt : ∀ D : D7, TransportSt D → CorrectionSt D := by
  exact @GlobalTheory.AdIsomCorrection.correction_of_transport
