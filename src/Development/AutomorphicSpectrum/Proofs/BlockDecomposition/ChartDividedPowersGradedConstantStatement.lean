import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_divided_powers_graded_constant : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  first | exact @GlobalTheory.CompanionTheory.ChartFil.chart_grConst | exact GlobalTheory.CompanionTheory.ChartFil.chart_grConst | (intros; apply GlobalTheory.CompanionTheory.ChartFil.chart_grConst <;> assumption)
