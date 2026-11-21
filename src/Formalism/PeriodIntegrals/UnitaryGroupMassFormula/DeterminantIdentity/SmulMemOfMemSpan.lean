import Mathlib

open NumberField

noncomputable section

namespace PI.DIP.Loc

variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

abbrev T : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl

theorem T_le : T K p ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
    (Ideal.primeCompl_le_nonZeroDivisors _)

abbrev A : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (T K p) (T_le K p)

variable {K p}

theorem mem_T {t : 𝓞 K} (ht : t ∈ T K p) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∃ u : 𝓞 K, (s : 𝓞 K) = u * t := by
  obtain ⟨z, hz, rfl⟩ := Submonoid.mem_map.mp ht
  have hz' : ¬ (p : ℤ) ∣ z := fun h => hz (Ideal.mem_span_singleton.mpr h)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, z = n ∨ z = -n := ⟨z.natAbs, Int.natAbs_eq z⟩
  have hcop : Nat.Coprime n p := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hz' ?_)
    have h' : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr h
    rcases hn with hn | hn <;> rw [hn]
    · exact h'
    · exact (dvd_neg).mpr h'
  refine ⟨n, hcop, ?_⟩
  rcases hn with hn | hn <;> subst hn
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end PI.DIP.Loc
