import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame

open NumberField IsDedekindDomain GlobalTheory.ShFam.Pad

namespace GlobalTheory.PlaceSum

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_eq_iff (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) :
    resP v = p ↔ ((p : 𝓞 F) ∈ v.asIdeal) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  unfold resP
  constructor
  · intro h
    have h0 : ((ringChar (𝓞 F ⧸ v.asIdeal) : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := ringChar.Nat.cast_ringChar
    rw [h, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  · intro h
    have h0 : (Ideal.Quotient.mk v.asIdeal (p : 𝓞 F)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [map_natCast] at h0
    have hd : ringChar (𝓞 F ⧸ v.asIdeal) ∣ p := ringChar.dvd h0
    rcases (Nat.dvd_prime hp).1 hd with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one (R := 𝓞 F ⧸ v.asIdeal))
    · exact h1

end GlobalTheory.PlaceSum
