import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometry
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  exact @GlobalTheory.StdIsom.stdIsomSt_of_rationalSt
