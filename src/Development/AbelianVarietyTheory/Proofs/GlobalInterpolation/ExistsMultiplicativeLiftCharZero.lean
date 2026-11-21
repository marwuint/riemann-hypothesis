import Mathlib

namespace GlobalTheory

theorem charZero_wittVector_of_field (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h3 : p ∣ l := (CharP.cast_eq_zero_iff K p l).1 h2
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h3
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

end GlobalTheory
