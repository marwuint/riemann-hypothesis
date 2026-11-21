import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_intersection_graded_iso : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapKC.cap_kc | exact GlobalTheory.CompanionTheory.CapKC.cap_kc | (intros; apply GlobalTheory.CompanionTheory.CapKC.cap_kc <;> assumption)
