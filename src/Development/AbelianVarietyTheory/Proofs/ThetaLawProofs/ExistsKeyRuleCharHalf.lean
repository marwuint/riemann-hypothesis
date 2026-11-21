import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIntegralKeyInvariantRuleCharZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFormulaPowOfKeyRuleCharZero

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTop

theorem exists_keyRule_charHalf :
    Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic →
      ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  intro hL hT hI hP hTor
  have hD : KeyDesc := (_root_.GlobalTheory.KeyCountableDescent.keyIn_descends_countable hL).2
  exact _root_.GlobalTheory.KeyHouse.keyRule_of_kaSt hL hT hI hP hTor (_root_.GlobalTheory.KaExists.kaSt hL hT hTor hD) hD

end GlobalTheory.KeyTop
