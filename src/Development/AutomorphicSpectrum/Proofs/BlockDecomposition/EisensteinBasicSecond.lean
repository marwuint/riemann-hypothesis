import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar partialLFunction)

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinEuler

open Classical in

def partialTerm (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) : Ideal (𝓞 ℚ) →* ℂ where
  toFun I := if ∀ v ∈ S, ¬ v.asIdeal ∣ I then c.coeffTerm s I else 0
  map_one' := by
    have h : ∀ v ∈ S, ¬ v.asIdeal ∣ (1 : Ideal (𝓞 ℚ)) := fun v _ hv =>
      v.isPrime.ne_top (Ideal.isUnit_iff.1 (isUnit_of_dvd_one hv))
    rw [if_pos h, map_one]
  map_mul' I J := by
    have hp : ∀ v : Pl, v.asIdeal ∣ I * J ↔ v.asIdeal ∣ I ∨ v.asIdeal ∣ J := fun v =>
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).dvd_mul
    by_cases hI : ∀ v ∈ S, ¬ v.asIdeal ∣ I
    · by_cases hJ : ∀ v ∈ S, ¬ v.asIdeal ∣ J
      · have hIJ : ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun v hv h =>
          ((hp v).1 h).elim (hI v hv) (hJ v hv)
        rw [if_pos hIJ, if_pos hI, if_pos hJ, map_mul]
      · have hIJ : ¬ ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun h =>
          hJ fun v hv hd => h v hv ((hp v).2 (Or.inr hd))
        rw [if_neg hIJ, if_neg hJ, mul_zero]
    · have hIJ : ¬ ∀ v ∈ S, ¬ v.asIdeal ∣ I * J := fun h =>
        hI fun v hv hd => h v hv ((hp v).2 (Or.inl hd))
      rw [if_neg hIJ, if_neg hI, zero_mul]

open Classical in
theorem partialTerm_apply (c : HeckeCharacter ℚ) (S : Finset Pl) (s : ℂ) (I : Ideal (𝓞 ℚ)) :
    partialTerm c S s I = if ∀ v ∈ S, ¬ v.asIdeal ∣ I then c.coeffTerm s I else 0 :=
  rfl

end GlobalTheory.CompanionTheory.RankinEuler

end
