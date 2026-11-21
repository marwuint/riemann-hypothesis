import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFinite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DcColSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.DoubleComplexMapMemTotal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDesc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCochainFiltrationDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_cech_cohomology_finite : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((cechH (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.main_thm | exact GlobalTheory.CompanionTheory.GrCech.main_thm | (intros; apply GlobalTheory.CompanionTheory.GrCech.main_thm <;> assumption)
