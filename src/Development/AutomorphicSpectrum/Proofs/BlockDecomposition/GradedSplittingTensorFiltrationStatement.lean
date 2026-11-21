import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingTensorFiltration
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_splitting_tensor_filtration : ∀ {O A Γ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing Γ] [Algebra O Γ] [Module.Flat O Γ]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m),
    ∃ g : (∀ i, S.N i ⊗[O] Γ) ≃ₗ[O] A ⊗[O] Γ, (∀ i n x, g (Pi.single i (n ⊗ₜ x)) = S.ν i n ⊗ₜ x) ∧
      ∀ (r : ℕ) (z : ∀ i, S.N i ⊗[O] Γ), g z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) ↔
        ∀ i : Fin m, (i : ℕ) < r → z i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.GrTens.main | exact GlobalTheory.CompanionTheory.GrTens.main | (intros; apply GlobalTheory.CompanionTheory.GrTens.main <;> assumption)
