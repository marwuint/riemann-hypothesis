import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardOpenSubgroupLeKerInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteEmbeddingMemStandardOpenSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscrNormConductorEqDFOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeff

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem fe_of_parts (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HeckeCharacter F)
    (hD : χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F)
    (hG : ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hG' : ∀ s : ℂ, (χ⁻¹).gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hR : χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * χ.continuedLFunction s =
      χ.coeff (differentIdeal ℤ (𝓞 F)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * (χ⁻¹).continuedLFunction (1 - s)) := by
  have nz : ∀ t : ℂ, (∀ n : ℕ, t ≠ -2 * n) → Complex.Gammaℝ t ≠ 0 := by
    intro t ht h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.1 h0
    exact ht n (by rw [hn]; ring)
  have key := χ.continuedLFunction_functional_equation (s := s)
    (by rw [hG]; exact pow_ne_zero _ (nz s h1))
    (by rw [hG']; exact pow_ne_zero _ (nz _ h2))
  rw [hG, hG', hD, hR] at key
  exact key

end GlobalTheory.CompanionTheory.PartialZeta
