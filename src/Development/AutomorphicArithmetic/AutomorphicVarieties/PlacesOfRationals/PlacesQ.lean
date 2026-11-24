module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.GenLeOfFintype

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Kum UpperTheory.V.B3

private theorem prime_l {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℤ)) := Nat.prime_iff_prime_int.mp hl
  rw [← MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃* ℤ)]
  simpa using h

private noncomputable def vQ {l : ℕ} (hl : l.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l hl).ne_zero).mpr (prime_l hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l hl).ne_zero

private theorem eq_vQ {l : ℕ} (hl : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    v = vQ hl := by
  apply HeightOneSpectrum.ext
  symm
  apply Ideal.IsMaximal.eq_of_le (vQ hl).isMaximal v.isPrime.ne_top
  show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal
  rwa [Ideal.span_le, Set.singleton_subset_iff]

private theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  set J : Ideal ℤ := v.asIdeal.comap (Int.castRingHom (𝓞 ℚ)) with hJ
  have hJp : J.IsPrime := Ideal.IsPrime.comap _
  have hJb : J ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hbot
    have hxe : ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) = x := by
      conv_rhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]
      exact (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
    have hmem : Rat.ringOfIntegersEquiv x ∈ J := by
      rw [hJ, Ideal.mem_comap]
      simpa [hxe] using hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    rw [← hxe, hmem]
    simp
  obtain ⟨z, hzJ, hz⟩ := hJp.exists_mem_prime_of_ne_bot hJb
  refine ⟨z.natAbs, Int.prime_iff_natAbs_prime.mp hz, ?_⟩
  have hz' : ((z.natAbs : ℤ)) ∈ J := by
    rcases Int.natAbs_eq z with h | h
    · rw [← h]; exact hzJ
    · have : ((z.natAbs : ℤ)) = -z := by omega
      rw [this]; exact J.neg_mem hzJ
  rw [hJ, Ideal.mem_comap] at hz'
  simpa using hz'

theorem UpperTheory.V.B3.placesQ :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω],
    (∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) ∧
    (∀ B : ValuationSubring Ω, Ine (F := ℚ) B = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ B.valuation (p : Ω) < 1) ∧
    ∀ (p : ℕ) (A B : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → B.valuation (p : Ω) < 1 →
      ∃ g : G ℚ Ω, ∀ x ∈ Ine (F := ℚ) B, g⁻¹ * x * g ∈ Ine (F := ℚ) A := by
  intro Ω _ _ _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have val_top {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
    by_contra hx
    have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
    rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
    exact lt_irrefl _ h2
  have int_le (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
      A.valuation b ≤ 1 := by
    have h : IsIntegral A b := hb.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [A.valuation_le_one_iff, ← hy]
    exact y.2
  have hTop : Ine (F := ℚ) (⊤ : ValuationSubring Ω) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  have hOver (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
      ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v := by
    have hm : ∀ x : 𝓞 ℚ, algebraMap ℚ Ω (x : ℚ) ∈ A := fun x =>
      (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap ℚ Ω).toIntAlgHom))
    let f : 𝓞 ℚ →+* A := ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)).codRestrict A hm
    let P : Ideal (𝓞 ℚ) := (IsLocalRing.maximalIdeal A).comap f
    have hP : ∀ x : 𝓞 ℚ, A.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ P := fun x =>
      (A.valuation_lt_one_iff (f x)).symm
    refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
    rw [eq_top_iff]
    intro x _
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    have h1 : Algebra.IsAlgebraic ℤ ℚ := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℚ)).2 inferInstance
    have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ ℚ Ω
    obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
    have h3 : ¬ A.valuation (algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ)) < 1 := by
      rw [hP, h0, Ideal.mem_bot]
      exact Int.cast_ne_zero.2 hn
    have h4 : A.valuation (n : Ω) = 1 :=
      le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
    have h5 := int_le A hi
    rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
    exact (A.valuation_le_one_iff x).1 h5
  have hNe (A : ValuationSubring Ω) (N : ℕ) (hN : N ≠ 0)
      (h : A.valuation (N : Ω) < 1) : A ≠ ⊤ := by
    intro he
    subst A
    exact hN (Nat.cast_eq_zero.1 (val_top h))
  have hIff (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ)
      (hv : IsPlaceOver A v) : A.valuation (N : Ω) < 1 ↔ ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have h := hv (N : 𝓞 ℚ)
    have e : algebraMap ℚ Ω ((N : 𝓞 ℚ) : ℚ) = (N : Ω) := by simp
    rwa [← e]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hA⟩ := exists_isPlaceOver (F := ℚ) Ω (vQ hp)
    exact ⟨A, (hIff A (vQ hp) p hA).mpr (Ideal.subset_span rfl)⟩
  · intro B
    by_cases hB : B = ⊤
    · left
      rwa [hB]
    · right
      obtain ⟨v, hv⟩ := hOver B hB
      obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
      exact ⟨p, hp, (hIff B v p hv).mpr hpv⟩
  · intro p A B hp hA hB
    obtain ⟨vA, hvA⟩ := hOver A (hNe A p hp.ne_zero hA)
    obtain ⟨vB, hvB⟩ := hOver B (hNe B p hp.ne_zero hB)
    have eA := eq_vQ hp vA ((hIff A vA p hvA).mp hA)
    have eB := eq_vQ hp vB ((hIff B vB p hvB).mp hB)
    subst eA
    rw [eB] at hvB
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hvA hvB
    refine ⟨σ, fun x hx => ?_⟩
    rw [← hσ] at hx
    exact GlobalTheory.Cut.ShaBound.conj_mem_Ine' hx
