import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparated
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specializes_of_pointLocalRing_le_separated : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X), locRing x ≤ locRing z → z ⤳ x := by
  exact @GlobalTheory.specializes_of_locRing_le
