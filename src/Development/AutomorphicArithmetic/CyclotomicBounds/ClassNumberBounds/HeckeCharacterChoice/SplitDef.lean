import Mathlib

open NumberField

namespace KStar.Choice

private theorem span_isPrime {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)

private theorem primesOver_finite (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).Finite := by
  have := span_isPrime hp
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal this (by simpa using hp.ne_zero)
  exact IsDedekindDomain.primesOver_finite _ _

end KStar.Choice
