import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDuality
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import ReciprocityTheory.Hypotheses.GalCoh
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, HOneTwo D := by
  exact @GlobalTheory.HOneTwoLevel.hOneTwo_holds
