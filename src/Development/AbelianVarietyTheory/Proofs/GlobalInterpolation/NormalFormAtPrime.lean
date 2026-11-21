import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NormalFormAtPrime

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Arith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem degOne_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hv : DegOne v)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : DegOne P := by
  have key : ∀ Q Q' : HeightOneSpectrum (𝓞 E), Q ≠ Q' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal → Q.asIdeal.under (𝓞 F) = v.asIdeal → DegOne Q := by
    intro Q Q' hne hm hQ
    have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← map_mul, ← hm, Ideal.absNorm_algebraMap, ← h2]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have hq : Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal :=
      (((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1)
    refine ⟨hq ▸ hv.1, ?_⟩
    rw [hq]
    intro hmem
    have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
      Ideal.dvd_span_singleton.2 hqv
    have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
      exact Ideal.dvd_span_singleton.2 hmem
    rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
    rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
    · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
    · have hle : I ≤ v.asIdeal := by
        rw [← hQ]
        exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
      apply hv.2
      rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
      exact Ideal.mul_mono_right hle
  obtain ⟨Q, Q', hne, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne hm hP
  · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne.symm (by rw [hm, mul_comm]) hP

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

theorem intAt_pow_mul {P : HeightOneSpectrum (𝓞 E)} (k : ℕ) {a : E} (ha : IntAt P a) : IntAt P ((qOf P : E) ^ k * a) := by
  refine IntAt.mul ?_ ha
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ k)

theorem intAt_pow_mono {P : HeightOneSpectrum (𝓞 E)} {A A' : ℕ} (h : A ≤ A') {a : E} (ha : IntAt P ((qOf P : E) ^ A * a)) :
    IntAt P ((qOf P : E) ^ A' * a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := intAt_pow_mul k ha
  rwa [← mul_assoc, ← pow_add, add_comm] at this

end Arith

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem sameDC_refl (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : SameDC (Pr := Pr) sharp j P h h :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem sameDC_trans {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h₁ h₂ : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h₁) (b : SameDC (Pr := Pr) sharp j P h₁ h₂) : SameDC (Pr := Pr) sharp j P h h₂ := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  obtain ⟨r', hr', k', hk', rfl⟩ := b
  exact ⟨r' * r, mul_mem hr' hr, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

def TwistDegOne (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1

theorem twistDegOne_of_isSel (h2 : Module.finrank X.F X.E = 2) (hsel : IsSel X sel) : TwistDegOne Pr sel mu := by
  classical
  rintro ⟨P, hP⟩ hn
  have hQ : P ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.1 hP).resolve_left hn
  unfold QE at hQ
  split_ifs at hQ with hf
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
    have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hf.mem_toFinset.1 hv
    have hg : GoodPl X.E S v := by
      by_contra hg
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 v)) hg
      exact hv' this
    exact degOne_of_split h2 hg.1 hg.2.1 (hsel v)
  · simp at hQ

variable {Ch sel mu}

variable (Ch sel mu)

end GlobalTheory.Proof.NormalFormAtPrime
