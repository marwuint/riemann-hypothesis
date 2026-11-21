import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BasisBase

def zK {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (t u : ℤ) (ht : t ≤ 0) (j : ℕ) : HdR q j →ₗ[K] HQ Q t u j :=
  ((toSq (sFil Q t) (sFil Q u) fun T => by
    change T.obj.pdPow t.toNat = ⊤
    rw [Int.toNat_of_nonpos ht, Thick.pdPow_zero]).pull j).comp (resK q Q j)

theorem zK_apply {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (t u : ℤ) (ht : t ≤ 0) (j : ℕ) (x : HdR q j) :
    zK q Q t u ht j x = (toSq (sFil Q t) (sFil Q u) fun T => by
      change T.obj.pdPow t.toNat = ⊤
      rw [Int.toNat_of_nonpos ht, Thick.pdPow_zero]).pull j (resK q Q j x) := rfl

end GlobalTheory.CompanionTheory.BasisBase
