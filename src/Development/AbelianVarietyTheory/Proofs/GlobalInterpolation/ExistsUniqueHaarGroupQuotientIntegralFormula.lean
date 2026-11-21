import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

theorem normaliseGroupClause_holds : NormaliseGroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ ν _ μ hμ
  exact _root_.GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ hμ

end GlobalTheory
