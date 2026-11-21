import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineSmoothFormsBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_smooth_forms_bijective : CrystallineSemistableComparison.Onto.AffOm → CrystallineSemistableComparison.Onto.OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e := by
  exact @GlobalTheory.CompanionTheory.OmGlue.om_top
