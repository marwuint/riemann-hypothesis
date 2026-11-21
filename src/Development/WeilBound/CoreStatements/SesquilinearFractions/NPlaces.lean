import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.SesquilinearFractions.NIdeal
import Development.WeilBound.CoreStatements.SesquilinearFractions.RatProductFormula
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

namespace NP

open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 k)) : ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
  have hP : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 k) ∈ v.asIdeal → ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd (by simpa using h) (v.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2)
    | prime q hq => intro _ h; exact ⟨⟨q, hq⟩, h⟩
    | mul a b ha hb =>
      intro hab h
      rw [Nat.cast_mul] at h
      rcases v.isPrime.mem_or_mem h with h | h
      · exact ha (fun h0 => hab (by rw [h0, zero_mul])) h
      · exact hb (fun h0 => hab (by rw [h0, mul_zero])) h
  exact hP _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem v.asIdeal)

theorem prime_unique (v : HeightOneSpectrum (𝓞 k)) {p q : Nat.Primes} (hp : ((p : ℕ) : 𝓞 k) ∈ v.asIdeal)
    (hq : ((q : ℕ) : 𝓞 k) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes p.2 q.2).2 fun h => hne (Subtype.ext h)
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 k))
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huw]
  simp only [eq_intCast, Int.cast_natCast]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hq)

theorem finite_over (p : Nat.Primes) : {v : HeightOneSpectrum (𝓞 k) | ((p : ℕ) : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((p : ℕ) : 𝓞 k)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end NP

end PositivityTheory.Xgf
