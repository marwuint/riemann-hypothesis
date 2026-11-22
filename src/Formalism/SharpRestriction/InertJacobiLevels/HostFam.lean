import Formalism.LocalRingCardinality.DataHost
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.TameInertiaTowers.TowerFieldFoundations
import Formalism.CyclotomicNorms.StatementI
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField
open scoped Pointwise

def Rt (s : ℕ) : Ranks where
  toFrame := Formalism.HC.cyclicFrame 2
  k := 8
  m := 2
  t := 2 * s + 15
  k_even := ⟨4, rfl⟩
  m_even := ⟨1, rfl⟩
  t_odd := ⟨s + 7, by ring⟩
  two_le_m := le_refl _
  m_add_three_le_k := by norm_num
  rank_add_five_le := by omega
  three_m_lt_t := by omega
  m_le_f := show 2 ≤ 2 * 2 ^ 2 by norm_num
  f_le_k := show 2 * 2 ^ 2 ≤ 8 by norm_num
  m_sq_le_N := by omega

theorem top_primitive {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    ¬ (⊤ : Ideal (𝓞 K)) ≤ Ideal.span {(m : 𝓞 K)} := by
  intro h
  have hu : IsUnit (m : 𝓞 K) := by
    rw [← Ideal.span_singleton_eq_top]; exact top_le_iff.1 h
  have hn : IsUnit (Algebra.norm ℤ (m : 𝓞 K)) := hu.map _
  rw [show (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap,
    Int.isUnit_iff] at hn
  have hr : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  have h2 : (2 : ℤ) ^ Module.finrank ℤ (𝓞 K) ≤ (m : ℤ) ^ Module.finrank ℤ (𝓞 K) :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm) _
  have h3 : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 K) := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Module.finrank ℤ (𝓞 K) := pow_le_pow_right₀ (by norm_num) hr
  rcases hn with h | h <;> omega

structure Arith (B N : ℕ) where
  q : ℕ
  d : ℕ
  hyp : HostHyp q d
  q_gt : N < q
  d_gt : N < d
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ B → jacobiSym (-(d : ℤ)) p = 1
  g0 : ℕ
  g1 : ℕ
  first_prime_isPrime : g0.Prime
  second_prime_isPrime : g1.Prime
  sixty_one_lt_first_prime : 61 < g0
  first_prime_lt_second : g0 < g1
  first_prime_modEq_one : g0 ≡ 1 [MOD 16 * q * d]
  second_prime_modEq_one : g1 ≡ 1 [MOD 16 * q * d]
  bb : Disjoint (Formalism.CyclotomicNorms.BB 9 g0) (Formalism.CyclotomicNorms.BB 9 g1)
  L : Type
  [instField : Field L]
  [instNF : NumberField L]
  ζ : L
  a : L
  b : L
  layer : IsLayer 4 q d ζ a b

attribute [instance] Arith.instField Arith.instNF

theorem frame2_inj : Function.Injective (Formalism.HC.cyclicFrame 2).h := Formalism.HC.frameCyc_h_injective 2 1

abbrev Arith.QS {B N : ℕ} (_ : Arith B N) : ℕ := 16

def Arith.ax {B N : ℕ} (A : Arith B N) : Formalism.HC.HostAx (Formalism.HC.cyclicFrame 2) :=
  Formalism.HC.D7.hostAx (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer

private theorem coprime_sixteen_of_mod {g q d : ℕ} (h : g ≡ 1 [MOD 16 * q * d]) : Nat.Coprime g 16 := by
  have h1 : g ≡ 1 [MOD 16] := (h.of_mul_right _).of_mul_right _
  rw [Nat.Coprime, h1.gcd_eq, Nat.gcd_one_left]

variable {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1))

theorem Arith.cm_nonempty : A.ax.cmType.Nonempty := by
  apply Set.nonempty_of_ncard_ne_zero
  rw [A.ax.der.cmType.2.1]
  have := (Formalism.HC.cyclicFrame 2).ord_pos
  omega

theorem Arith.bb_ex : ∃ 𝔟 : Ideal (𝓞 A.ax.E),
    differentIdeal (𝓞 A.ax.K) (𝓞 A.ax.E) = 𝔟 * (A.ax.conj • 𝔟) ∧ 𝔟 ⊔ A.ax.conj • 𝔟 = ⊤ ∧
    ∀ σ : A.ax.E ≃ₐ[ℚ] A.ax.E, A.ax.gal σ ∈ (Formalism.HC.cyclicFrame 2).Psi → σ • 𝔟 = 𝔟 :=
  A.ax.der.principal

private theorem gal_sqq_ax (φ : Formalism.HC.Frame) (hinj : Function.Injective φ.h) {q d : ℕ} (hH : HostHyp q d)
    (he : 2 ≤ φ.e) {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (φ.e + 2) q d ζ a b)
    (σ : (Formalism.HC.D7.hostRaw φ hinj hH he h).E ≃ₐ[ℚ] (Formalism.HC.D7.hostRaw φ hinj hH he h).E) :
    σ (Formalism.HC.D7.sqq φ hinj hH he h) =
      (((((Formalism.HC.D7.hostRaw φ hinj hH he h).gal σ).1.1 : ℤˣ) : ℤ) : (Formalism.HC.D7.hostRaw φ hinj hH he h).E) *
        Formalism.HC.D7.sqq φ hinj hH he h :=
  Formalism.HC.D7.gal_sqq φ hH h σ

def hostOf (u0 : (Rt s).A) (T Lw : ℕ) : Host (Rt s) where
  toHostAx := A.ax
  flPS := Formalism.HC.D7.psQ (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  sqq := Formalism.HC.D7.sqq (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  sqq_sq := Formalism.HC.D7.sqq_sq (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  gal_sqq := gal_sqq_ax (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  QS_exact := Formalism.HC.D7.exact (Formalism.HC.cyclicFrame 2) frame2_inj A.hyp le_rfl A.layer
  QS_le := show 2 ^ (2 + 2) ≤ (2 ^ 2) ^ 2 by norm_num
  o_pow := (congrArg (· ^ 64) (Formalism.HC.cyclicFrame_index 2)).trans_le ((one_pow 64).trans_le Nat.one_le_two_pow)
  q_ne_three := by have := A.q_gt; show A.q ≠ 3; omega
  qd_big := ⟨A.q_gt, A.d_gt⟩
  splitBound := B
  split_small := A.split
  small_le := fun l hl h2 hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (n := 2 + 2) hd)) h2
  φ₀ := A.cm_nonempty.some
  φ₀_mem := A.cm_nonempty.some_mem
  𝔟 := A.bb_ex.choose
  𝔟_spec := ⟨A.bb_ex.choose_spec.1, A.bb_ex.choose_spec.2.1⟩
  𝔟_stable := A.bb_ex.choose_spec.2.2
  levelPrimes := {31, 61, A.g0, A.g1} ∪ ({T} : Finset ℕ).filter (fun p => Nat.Coprime p 16)
  g := ![A.g0, A.g1]
  g_prime := by intro i; fin_cases i; exacts [A.first_prime_isPrime, A.second_prime_isPrime]
  g_ne := by simpa using A.first_prime_lt_second.ne
  g_level := by intro i; fin_cases i <;> simp
  pde := 31
  pde' := 61
  pde_prime := by norm_num
  pde'_prime := by norm_num
  pde_ne := by norm_num
  pde_level := by simp
  pde_mod := by norm_num
  pde_ne_g := by
    have := A.sixty_one_lt_first_prime; have := A.first_prime_lt_second
    intro i; fin_cases i <;> simp <;> omega
  ccK := ⊤
  ccK_ne_bot := top_ne_bot
  ccK_primitive := fun m hm => top_primitive m hm
  ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
  ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
  ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
  level_coprimeS := by
    intro p hp
    show Nat.Coprime p 16
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hp
    rcases hp with (rfl | rfl | rfl | rfl) | h
    · norm_num
    · norm_num
    · exact coprime_sixteen_of_mod A.first_prime_modEq_one
    · exact coprime_sixteen_of_mod A.second_prime_modEq_one
    · exact h.2
  TT := ∅
  T2 := {0}
  u0 := u0
  Lw := Lw + 4
  two_le_Lw := by omega
  second_set_range := by intro j hs; simp at hs; subst hs; rw [show (Rt s).toFrame.n0 = 2 ^ 2 from Formalism.HC.cyclicFrame_order 2]; simp
  second_set_no_relation := by
    intro s₁ h₁ s₂ h₂ _ _ h12
    simp at h₁ h₂
    exact absurd (h₁.trans h₂.symm) h12
  CT2 := 0

end Formalism.MainNotions.Inhab

end
