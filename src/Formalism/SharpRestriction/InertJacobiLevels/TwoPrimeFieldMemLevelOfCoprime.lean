import Formalism.SharpRestriction.InertJacobiLevels.PrimeSupply
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

section General

variable {R : Ranks} (H : Host R)

theorem primesOver_ncard (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = (placesOver E p).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have himg : (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' placesOver E p =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) := by
    ext I
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ⟨?_⟩⟩
      have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 E) p ∈ v.asIdeal
        have hv' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
        simpa using hv'
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      have hmem : ((p : ℕ) : 𝓞 E) ∈ I := by
        have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _
        simpa using this
      have hne : I ≠ ⊥ := by
        rintro rfl
        have h0 : ((p : ℕ) : 𝓞 E) = 0 := by simpa using hmem
        exact hp.ne_zero (by exact_mod_cast h0)
      exact ⟨⟨I, hI, hne⟩, hmem, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

end General

theorem form_mod {T M d : ℕ} {u v : ℤ} (hT : (T : ℤ) = (1 + M * u) ^ 2 + d * (M * v) ^ 2) : T ≡ 1 [MOD M] := by
  rw [← Int.natCast_modEq_iff]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact ⟨2 * u + M * u ^ 2 + d * M * v ^ 2, by rw [hT]; push_cast; ring⟩

def Yof (R : Ranks) (x eps : ℝ) : ℝ := ((R.k : ℝ) * Real.exp (x ^ eps)) ^ 8

structure Fld (R : Ranks) (x eps : ℝ) extends Formalism.HC.HostAx R.toFrame where
  flPS : toHostRaw.PsQ
  sqq : E
  sqq_sq : sqq ^ 2 = -(q : E)
  gal_sqq : ∀ σ : E ≃ₐ[ℚ] E, σ sqq = ((((gal σ).1.1 : ℤˣ) : ℤ) : E) * sqq
  QS_exact : toHostRaw.Exact
  QS_le : QS ≤ R.n ^ 2
  o_pow : R.toFrame.o ^ 64 ≤ 2 ^ R.e
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → 4 * l ≤ ⌊x ^ (eps / 5)⌋₊
  good : QDGood x eps q d
  o_tie : (R.o : ℝ) ≤ x ^ (eps / 1000)
  QS_tie : (QS : ℝ) ≤ 4 * R.n * x ^ (eps / 1000)

structure Base (R : Ranks) (x eps Cp CT : ℝ) extends Fld R x eps where
  q_big : 4 * R.t * R.r + 1 < q
  d_big : 4 * R.t * R.r + 1 < d
  g0 : ℕ
  g1 : ℕ
  first_prime_isPrime : g0.Prime
  second_prime_isPrime : g1.Prime
  g_ne : g0 ≠ g1
  first_prime_in_window : Yof R x eps ≤ g0 ∧ (g0 : ℝ) ≤ 2 * Yof R x eps
  second_prime_in_window : Yof R x eps ≤ g1 ∧ (g1 : ℝ) ≤ 2 * Yof R x eps
  first_prime_norm_form : ∃ u v : ℤ, (g0 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  second_prime_norm_form : ∃ u v : ℤ, (g1 : ℤ) = (1 + (QS * q * d : ℕ) * u) ^ 2 + d * ((QS * q * d : ℕ) * v) ^ 2
  bb : Disjoint (Formalism.CyclotomicNorms.BB R.r g0) (Formalism.CyclotomicNorms.BB R.r g1)
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_mod : pde ≡ 1 [MOD 15 * (QS * q * d)]
  pde'_mod : pde' ≡ 1 [MOD 15 * (QS * q * d)]
  pde_ne_g : pde ≠ g0 ∧ pde ≠ g1 ∧ pde' ≠ g0 ∧ pde' ≠ g1
  pde_log : Real.log pde < x ^ (eps / 3) ∧ Real.log pde' < x ^ (eps / 3)
  Cp_pos : 0 < Cp
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  T2 : Finset ℕ
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < R.n0
  second_set_no_relation : NoRel T2 Lw
  T2_card : (R.n0 : ℝ) * Real.exp (-(CT * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log Lw))) / Lw ≤ T2.card
  TT : Finset (R.A)

variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

theorem cm_nonempty : B.cmType.Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [B.der.cmType.2.1]
  positivity

theorem bb_ex : ∃ 𝔟 : Ideal (𝓞 B.E),
    differentIdeal (𝓞 B.K) (𝓞 B.E) = 𝔟 * (B.conj • 𝔟) ∧ 𝔟 ⊔ B.conj • 𝔟 = ⊤ ∧
    ∀ σ : B.E ≃ₐ[ℚ] B.E, B.gal σ ∈ R.Psi → σ • 𝔟 = 𝔟 :=
  B.der.principal

theorem coprime_QS_of_mod {p : ℕ} (h : p ≡ 1 [MOD B.QS * B.q * B.d]) : Nat.Coprime p B.QS := by
  have h1 : p ≡ 1 [MOD B.QS] := h.of_dvd ⟨B.q * B.d, by ring⟩
  rw [Nat.Coprime, h1.gcd_eq, Nat.gcd_one_left]

end Base

def host2 (u0 : R.A) (ex : Finset ℕ) : Host R where
  toHostAx := B.toHostAx
  flPS := B.flPS
  sqq := B.sqq
  sqq_sq := B.sqq_sq
  gal_sqq := B.gal_sqq
  QS_exact := B.QS_exact
  QS_le := B.QS_le
  o_pow := B.o_pow
  small_le := B.small_le
  q_ne_three := by
    have h := B.q_big
    have ht : 1 ≤ R.t := by have := R.rank_add_five_le; omega
    have hr : 1 ≤ R.r := by have := R.two_le_m; unfold Ranks.r; omega
    have h1 : 1 ≤ R.t * R.r := Nat.mul_pos ht hr
    have e : 4 * R.t * R.r = 4 * (R.t * R.r) := by ring
    omega
  qd_big := ⟨B.q_big, B.d_big⟩
  splitBound := ⌊x ^ (eps / 5)⌋₊
  split_small := fun p hp h2 hB => B.good.split p hp h2 (by
    rcases Nat.eq_zero_or_pos ⌊x ^ (eps / 5)⌋₊ with h0 | h0
    · rw [h0] at hB; exact absurd hp.pos (by omega)
    · exact (Nat.cast_le.2 hB).trans (Nat.floor_le (Nat.pos_of_floor_pos h0).le))
  φ₀ := B.cm_nonempty.some
  φ₀_mem := B.cm_nonempty.some_mem
  𝔟 := B.bb_ex.choose
  𝔟_spec := ⟨B.bb_ex.choose_spec.1, B.bb_ex.choose_spec.2.1⟩
  𝔟_stable := B.bb_ex.choose_spec.2.2
  levelPrimes := {B.g0, B.g1, B.pde, B.pde'} ∪ ex.filter (fun p => Nat.Coprime p B.QS)
  g := ![B.g0, B.g1]
  g_prime := by intro i; fin_cases i; exacts [B.first_prime_isPrime, B.second_prime_isPrime]
  g_ne := by simpa using B.g_ne
  g_level := by intro i; fin_cases i <;> simp
  pde := B.pde
  pde' := B.pde'
  pde_prime := B.pde_prime
  pde'_prime := B.pde'_prime
  pde_ne := B.pde_ne
  pde_level := by simp
  pde_mod := ⟨B.pde_mod.of_mul_right _, B.pde'_mod.of_mul_right _⟩
  pde_ne_g := by
    obtain ⟨h1, h2, h3, h4⟩ := B.pde_ne_g
    intro i; fin_cases i
    · exact ⟨h1, h3⟩
    · exact ⟨h2, h4⟩
  ccK := ⊤
  ccK_ne_bot := top_ne_bot
  ccK_primitive := fun m hm => top_primitive m hm
  ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
  ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
  ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
  level_coprimeS := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hp
    rcases hp with (rfl | rfl | rfl | rfl) | h
    · obtain ⟨u, v, h⟩ := B.first_prime_norm_form; exact B.coprime_QS_of_mod (form_mod h)
    · obtain ⟨u, v, h⟩ := B.second_prime_norm_form; exact B.coprime_QS_of_mod (form_mod h)
    · exact B.coprime_QS_of_mod (B.pde_mod.of_mul_left _)
    · exact B.coprime_QS_of_mod (B.pde'_mod.of_mul_left _)
    · exact h.2
  TT := B.TT
  T2 := B.T2
  u0 := u0
  Lw := B.Lw
  two_le_Lw := B.two_le_Lw
  second_set_range := B.second_set_range
  second_set_no_relation := B.second_set_no_relation
  CT2 := CT

theorem twoPrimeField_levelPrimes (u0 : R.A) (ex : Finset ℕ) : (host2 B u0 ex).levelPrimes =
    {B.g0, B.g1, B.pde, B.pde'} ∪ ex.filter (fun p => Nat.Coprime p B.QS) := rfl

end Formalism.MainNotions.Inhab

end
