import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem tameAnyFix_map_primeToPart {M K : Type} [Monoid M] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l]
    (ι : M →* K) (x : M) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  have hl : l.Prime := Fact.out
  unfold Formalism.CyclotomicNorms.primeToPart
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0]
    have e : ∀ n : ℕ, n = 0 → (((1 : ℕ) : ZMod n)⁻¹).val = 1 := by
      intro n hn
      subst hn
      rw [Nat.cast_one, ZMod.inv_one]
      rfl
    have e0 : l ^ (Nat.factorization 0) l = 1 := by simp
    rw [e0, e _ (by simp)]
    simp
  · set a := (orderOf x).factorization l with ha
    set m := orderOf x / l ^ a with hm
    have hmul : l ^ a * m = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : Nat.Coprime (l ^ a) m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
    have hmpos : 0 < m := Nat.ordCompl_pos l hpos.ne'
    haveI : NeZero m := ⟨hmpos.ne'⟩
    have h1 : (ι x ^ m) ^ l ^ a = 1 ^ l ^ a := by
      rw [← pow_mul, mul_comm, hmul, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
    have h2 : ι x ^ m = 1 := by
      have := iterateFrobenius_inj K l a
      exact this (by simpa [iterateFrobenius_def] using h1)
    have h3 : l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast [ZMod.natCast_zmod_val]
      have := ZMod.coe_mul_inv_eq_one (l ^ a) hcop
      simpa using this
    rw [map_pow]
    have h4 : ι x ^ (l ^ a * (((l ^ a : ℕ) : ZMod m)⁻¹).val) = ι x ^ 1 := by
      rw [pow_eq_pow_mod _ h2, h3, ← pow_eq_pow_mod _ h2]
    rw [h4, pow_one]

theorem tameAnyFix_isoLoc (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem tameAnyFix_not_over (D : D7) (i : D.nd.Loc) (k : Fin 2) (h : D.nd.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
  intro hl
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hl' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := hl
  have hc : Nat.Coprime (D.nd.l i) (D.host.g k) := (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 h
  have hc' : IsCoprime ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hc
  obtain ⟨a, b, hab⟩ := hc'
  apply (D.naut.plGw k v).isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl') (Ideal.mul_mem_left _ _ hg)

end GlobalTheory.TypeLeaf
