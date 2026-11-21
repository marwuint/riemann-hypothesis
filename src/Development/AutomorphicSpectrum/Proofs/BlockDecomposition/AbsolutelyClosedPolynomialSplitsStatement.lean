import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedPolynomialSplits
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_closed_polynomial_splits : ∀ {S : Type} [CommRing S] , Aic S → ∀ P : Polynomial S, P.Monic → ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  exact @GlobalTheory.CompanionTheory.MonicSplit.monic_splits
