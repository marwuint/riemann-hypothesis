import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

noncomputable section

namespace UpperTheory.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField
open scoped Pointwise

theorem top_not_le_span {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
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

def withTop {R : Ranks} (H : Host R) : Host R :=
  { H with
    ccK := ⊤
    ccK_ne_bot := top_ne_bot
    ccK_primitive := fun m hm => top_not_le_span m hm
    ccK_split := fun _ hP hle => absurd (top_le_iff.1 hle) hP.ne_top
    ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
    ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _ }

theorem withTop_ccK {R : Ranks} (H : Host R) : (withTop H).ccK = ⊤ := rfl

end UpperTheory.Host

end
