import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatumAOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory AlgebraicGeometry

open scoped NumberField TensorProduct
open GlobalTheory.UPel.HT

namespace GlobalTheory.IwLevel.IwInhab

theorem five_not_unit : ¬ IsUnit ((5 : ℕ) : 𝓞 gaussOneDatum.F) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ)
  have h2 : Algebra.norm ℤ ((5 : ℕ) : 𝓞 gaussOneDatum.F) = (5 : ℤ) ^ Module.finrank ℤ (𝓞 gaussOneDatum.F) := by
    rw [← map_natCast (algebraMap ℤ (𝓞 gaussOneDatum.F)), Algebra.norm_algebraMap]; norm_num
  rw [h2] at h1
  have hpos : Module.finrank ℤ (𝓞 gaussOneDatum.F) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hpos, Int.isUnit_iff] at h1
  omega

def wG : Ideal (𝓞 gaussOneDatum.F) :=
  Classical.choose (Ideal.exists_le_maximal (Ideal.span {((5 : ℕ) : 𝓞 gaussOneDatum.F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact five_not_unit))

theorem wG_spec : Ideal.span {((5 : ℕ) : 𝓞 gaussOneDatum.F)} ≤ wG ∧ wG.IsMaximal :=
  (Classical.choose_spec (Ideal.exists_le_maximal (Ideal.span {((5 : ℕ) : 𝓞 gaussOneDatum.F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact five_not_unit))).symm

theorem five_mem : ((5 : ℕ) : 𝓞 gaussOneDatum.F) ∈ wG := wG_spec.1 (Ideal.mem_span_singleton_self _)

instance wG_max : wG.IsMaximal := wG_spec.2
instance wG_prime : wG.IsPrime := wG_max.isPrime

theorem five_ne_zero : ((5 : ℕ) : 𝓞 gaussOneDatum.F) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)

theorem wG_ne_bot : wG ≠ ⊥ := fun h => by
  have := five_mem
  rw [h, Ideal.mem_bot] at this
  exact five_ne_zero this

abbrev RG : Type := Localization.AtPrime wG

instance : IsDiscreteValuationRing RG :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ wG_ne_bot _

end GlobalTheory.IwLevel.IwInhab
