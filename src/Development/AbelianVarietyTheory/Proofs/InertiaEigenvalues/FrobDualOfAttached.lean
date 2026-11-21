import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleFrobDual

theorem charpoly_smul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • M).charpoly = (m.map fun β => X - C (c * β)).prod := by
  have h1 := GlobalTheory.ConjPoly.charpoly_smul_inv M N h m 1 hM
  have h2 := GlobalTheory.ConjPoly.charpoly_smul_inv N M (mul_eq_one_comm.1 h) (m.map (·⁻¹)) c
    (by rw [one_smul] at h1; rw [h1, Multiset.map_map]; simp)
  rw [h2, Multiset.map_map]
  simp

theorem cyclotomicChar_frobenius_eq_normPlace {D : D7} (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∉ placesOver D.host.E (D.ntw.l i)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A v)
    {σ : Gen.GE D.nd} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  have h := cycZ_of_isFrob hv hA hσ
  change algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : _) = _
  rw [h, map_natCast]

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective _ _)

end GlobalTheory.TripleFrobDual
