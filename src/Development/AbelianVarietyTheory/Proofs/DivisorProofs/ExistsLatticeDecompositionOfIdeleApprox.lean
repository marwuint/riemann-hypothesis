import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

namespace GlobalTheory.LatDecomp

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem finiteAdeleMap_algebraMap (a : K) :
    finiteAdeleMap K E (algebraMap K (Af K) a) = algebraMap E (Af E) (algebraMap K E a) :=
  FiniteAdeleRing.ext _ fun w => finiteCompletionMap_coe K E w a

theorem finiteAdeleMap_integral {z : Af K} (hz : ∀ v, Valued.v (z v) ≤ 1) (w : HeightOneSpectrum (𝓞 E)) :
    (finiteAdeleMap K E z) w ∈ w.adicCompletionIntegers E :=
  finiteCompletionMap_mapsTo K E w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz _))

theorem algebraMap_integral (s : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (s : E)) w ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_le_one s

theorem exists_nat_mul_integral (a : Af E) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ w, ((d : Af E) * a) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨β, hβ0, hβ⟩ := GlobalTheory.Idele.exists_mul_integral (R := 𝓞 E) (K := E) a
  have hmem : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : 𝓞 E) ∈ Ideal.span {β} := Ideal.absNorm_mem _
  obtain ⟨g0, hg0⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨Ideal.absNorm (Ideal.span {β}), ?_, fun w => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hβ0
  · have e : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : Af E) =
        algebraMap E (Af E) ((g0 : 𝓞 E) : E) * algebraMap E (Af E) (algebraMap (𝓞 E) E β) := by
      rw [← map_mul]
      have := congrArg (fun r : 𝓞 E => algebraMap E (Af E) (r : E)) hg0
      simp only [map_natCast] at this
      rw [← this]; push_cast; rfl
    rw [e, _root_.mul_assoc]
    exact mul_mem (algebraMap_integral g0 w) ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hβ w))

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_good {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) (e : E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z : Af E, (∀ w, z w ∈ w.adicCompletionIntegers E) →
      z * algebraMap E (Af E) ((N : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_integral (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E))
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm c * d, Nat.mul_ne_zero hN hd0, fun z hz => ?_⟩
  have h := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c)
    (y := z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) (fun w => mul_mem (hz w) (hd w))
  have e1 : z * algebraMap E (Af E) (((Ideal.absNorm c * d : ℕ) : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) =
      algebraMap E (Af E) (algebraMap (OF E) E ((Ideal.absNorm c : ℕ) : OF E)) *
        (z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) := by
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e1]; exact h

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

end GlobalTheory.LatDecomp

