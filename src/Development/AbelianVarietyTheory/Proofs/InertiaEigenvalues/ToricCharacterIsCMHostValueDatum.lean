import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem toricCharacter_isCMHostValueDatum : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  intro D Z hZ l j a s hs hN
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, hind⟩ := _root_.GlobalTheory.LamTie.CMType.phi_cmType D.R D.host
  obtain ⟨hκ, hinf⟩ := GlobalTheory.T.one_le_kap_and_lam0_hasInf D Z hZ l j a s hN
  obtain ⟨hu, ht⟩ := _root_.GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield D Z hZ l j a
  have hb : IsBaseCond (cond0 D.host Z.w0) :=
    _root_.GlobalTheory.LamTie.isBaseCond_cond0 D.R D.host Z.q0 Z.w0 (fun p hp P hP => by
      obtain ⟨h1, -, h3, h4⟩ := hZ.places.splits p hp
      exact _root_.GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm D.host.E p h1 h3 h4 P hP) hZ.places
  refine ⟨hcm, hind, hs, hκ, hb, hu, ht, hinf, fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty v), fun _ => ?_⟩⟩
  have hv : v = below P := HeightOneSpectrum.ext (hP.symm.trans (over_below P))
  subst hv
  exact _root_.GlobalTheory.LamTie.lam0_expAt D Z hZ l j a P

end GlobalTheory.LamTie
