import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsValuedHeckeCharRamified

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp c_vp cE_vp a0 n_vp)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsInvIdealOf IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.LatVal.Model

variable {K : Type} [Field K] [NumberField K]

theorem int_iff (x : K) : (∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((algebraMap K (Af K) x) v) ≤ 1) ↔
    x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have e : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((algebraMap K (Af K) x) v) = v.valuation K x := fun v =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  simp only [e, FractionalIdeal.mem_one_iff]
  constructor
  · intro h
    exact HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x h
  · rintro ⟨r, rfl⟩ v
    exact v.valuation_le_one r

theorem exists_isLatOf (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) :
    ∃ Λ : PeriodPair, IsLatOf ι 1 Λ := by
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, h2]; simp
  let e := Fintype.equivOfCardEq hc
  let b := (RingOfIntegers.basis K).reindex e
  let B := (integralBasis K).reindex e
  have hB : ∀ i, B i = algebraMap (𝓞 K) K (b i) := fun i => by simp [B, b]
  have hrep : ∀ x : K, ∃ p q : ℚ, ι x = p * ι (B 0) + q * ι (B 1) := fun x => by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    simp [Fin.sum_univ_two, Rat.smul_def]
  have hδ' : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hind : LinearIndependent ℝ ![ι (B 0), ι (B 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Complex.real_smul] at h
    obtain ⟨p, q, h1⟩ := hrep 1
    obtain ⟨p', q', h3⟩ := hrep δ
    rw [map_one] at h1
    have key : ∀ u w : ℝ, (u : ℂ) * ι δ = w → u = 0 := fun u w huw => by
      have : ((u : ℂ) * ι δ) ^ 2 = (w : ℂ) ^ 2 := by rw [huw]
      rw [mul_pow, hδ'] at this
      have h' : u ^ 2 * (-(d : ℝ)) = w ^ 2 := by exact_mod_cast this
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      have : u ^ 2 ≤ 0 := by nlinarith [sq_nonneg w, sq_nonneg u]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg u))
    have k1 := key (s * q - t * p) (s * q' - t * p') (by
      push_cast
      have : ((s : ℂ) * q' - t * p') = ((s : ℂ) * q' - t * p') * 1 := by ring
      rw [this, h1, h3]
      linear_combination (q * p' - p * q' : ℂ) * h)
    have k1' : (s : ℂ) * q - t * p = 0 := by exact_mod_cast k1
    have hb0 : ι (B 0) ≠ 0 := by simpa using B.ne_zero 0
    have hb1 : ι (B 1) ≠ 0 := by simpa using B.ne_zero 1
    have hs : (s : ℂ) = 0 := by linear_combination (s : ℂ) * h1 + (p : ℂ) * h + ι (B 1) * k1'
    have ht : (t : ℂ) = 0 := by linear_combination (t : ℂ) * h1 + (q : ℂ) * h - ι (B 0) * k1'
    exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩
  refine ⟨⟨ι (B 0), ι (B 1), hind⟩, ?_⟩
  ext z
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m * b 0 + n * b 1, rfl⟩, by simp [hB]⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨b.repr r 0, b.repr r 1, ?_⟩
    conv_rhs => rw [← b.sum_repr r]
    simp [Fin.sum_univ_two, hB]

end GlobalTheory.LatVal.Model
