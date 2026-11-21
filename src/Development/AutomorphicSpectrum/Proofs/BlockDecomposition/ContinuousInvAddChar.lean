import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotientStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedRankQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibreStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import GroundTheory.AutomorphicForms.FiniteLengthLattice
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmoothStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideMore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotient

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

end Proofs

end GlobalTheory.CompanionTheory.BZCuspPair
