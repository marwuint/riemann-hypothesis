import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Neutral.B1
  GlobalTheory.HeckeGal

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tame

variable {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 M)}

theorem normV_mem (v : HeightOneSpectrum (𝓞 M)) : ((normV v : ℕ) : 𝓞 M) ∈ v.asIdeal := by
  have : Finite (𝓞 M ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 M ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 M ⧸ v.asIdeal) : ℕ) : 𝓞 M ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hc

omit [IsAlgClosure M Ω] in

theorem weil_fix_root (h : IsPlaceOver A v) (s : Weil h) (ζ : Ω) (hζ : ζ ^ (normV v - 1) = 1) :
    (s : G M Ω) ζ = ζ := by
  have hq : 1 < normV v := one_lt_normV v
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow (n := normV v - 1) (by omega) (by rw [hζ]; exact isIntegral_one)
  have hζA : A.valuation ζ ≤ 1 := (A.valuation_le_one_iff _).2 (ReciprocityTheory.Gal.mem_of_isIntegral_int A hζi)
  have hζ1 : ζ ^ normV v = ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have hpow : ∀ (y : Ω), y ^ normV v = y → ∀ k : ℕ, y ^ (normV v ^ k) = y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hy]
  have hsζ : ((s : G M Ω) ζ) ^ (normV v - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hsζ1 : ((s : G M Ω) ζ) ^ normV v = (s : G M Ω) ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hsζ, one_mul]
  obtain ⟨a, b, hab⟩ := s.2
  have hc := hab.2 ζ hζA
  rw [hpow _ hsζ1, hpow _ hζ1] at hc
  have hsA : A.valuation ((s : G M Ω) ζ) ≤ 1 := by
    rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hab.1, ← A.valuation_le_one_iff]
    exact hζA
  have hval1 : A.valuation ζ = 1 := by
    refine le_antisymm hζA (not_lt.1 fun hlt => ?_)
    have := pow_lt_one₀ zero_le hlt (show normV v - 1 ≠ 0 by omega)
    rw [← map_pow, hζ, map_one] at this
    exact lt_irrefl _ this
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (h ((normV v : ℕ) : 𝓞 M)).2 (normV_mem v)
    simpa using this
  have hd : ¬ A.valuation (aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X]))) < 1 := by
    have e : aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X])) =
        (((normV v - 1 : ℕ) : Ω)) * ζ ^ (normV v - 1 - 1) := by
      simp [derivative_X_pow]
    rw [e, map_mul, map_pow, hval1, one_pow, mul_one]
    have e2 : (((normV v - 1 : ℕ) : Ω)) = -1 + ((normV v : ℕ) : Ω) := by
      rw [Nat.cast_sub hq.le]; ring
    have h' : A.valuation ((normV v : ℕ) : Ω) < A.valuation (-1 : Ω) := by
      rw [Valuation.map_neg, map_one]; exact hqA
    rw [e2, Valuation.map_add_eq_of_lt_left _ h', Valuation.map_neg, map_one]
    exact lt_irrefl _
  exact (GlobalTheory.eq_of_root_congr_of_deriv_unit A (X ^ (normV v - 1) - 1) ζ ((s : G M Ω) ζ) hζA hsA
    (by simp [hζ]) (by simp [hsζ]) hd (by rw [Valuation.map_sub_swap]; exact hc)).symm

end Tame

end DiscreteGroups.sglob.DzType
