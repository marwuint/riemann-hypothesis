import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.NormCoprime

theorem coprime_absNorm_of_sup {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (h : I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm I) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let _ : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 K)} := by rw [h]; trivial
  obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hpx : (p : ℕ) • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hq : (Ideal.Quotient.mk I i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have hx0 : x = 0 := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have e0 : y = i * y + t * (((p : ℕ) : 𝓞 K) * y) := by linear_combination (-(y)) * hir
    have e : Ideal.Quotient.mk I y = Ideal.Quotient.mk I i * Ideal.Quotient.mk I y +
        Ideal.Quotient.mk I t * ((p : ℕ) • Ideal.Quotient.mk I y) := by
      rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk I) p, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← e0]
    rw [e, hpx, mul_zero, add_zero, hq, zero_mul]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

end GlobalTheory.NormCoprime
