import Mathlib

namespace Bl.general_b_fact_third_version

open NumberField in
theorem goal1
    {E : Type} [inst : Field E] [NumberField E] {V : Type}
    [inst_2 : AddCommGroup V] [inst_3 : Module E V] [inst_4 : Module (RingOfIntegers E) V]
    [inst_5 : IsScalarTower (RingOfIntegers E) E V] (Λ : Submodule (RingOfIntegers E) V) :
    Submodule.IsLattice E Λ → ∀ v : V, ∃ m : ℕ, m ≠ 0 ∧ (m : E) • v ∈ Λ := by
  intro hΛ v
  have key : ∀ c : E, ∃ m : ℕ, m ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      (m : E) * c = algebraMap (NumberField.RingOfIntegers E) E a := by
    intro c
    have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (IsAlgebraic.of_finite ℚ c)
    obtain ⟨m, s, hm, h⟩ := hc.exists_nsmul_eq (NumberField.RingOfIntegers E)
    exact ⟨m, hm, s, by rw [← h, nsmul_eq_mul]⟩
  have h1 : ∀ (k : ℕ) (w : V), w ∈ Λ → (k : E) • w ∈ Λ := fun k w hw => by
    rw [Nat.cast_smul_eq_nsmul]; exact Λ.nsmul_mem hw k
  let S : Submodule E V :=
    { carrier := {w | ∃ m : ℕ, m ≠ 0 ∧ (m : E) • w ∈ Λ}
      add_mem' := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        rw [Nat.cast_mul, smul_add]
        refine Λ.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact h1 _ _ ha
        · rw [mul_smul]; exact h1 _ _ hb
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c w ⟨m, hm, hw⟩
        obtain ⟨n, hn, a, ha⟩ := key c
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        have e : ((n * m : ℕ) : E) • (c • w) = a • ((m : E) • w) := by
          rw [← algebraMap_smul E a ((m : E) • w), ← ha, Nat.cast_mul, smul_smul, smul_smul]
          congr 1; ring
        rw [e]; exact Λ.smul_mem a hw }
  have hle : Submodule.span E (Λ : Set V) ≤ S :=
    Submodule.span_le.mpr (fun w hw => ⟨1, one_ne_zero, by simpa using hw⟩)
  rw [hΛ.span_eq_top] at hle
  obtain ⟨m, hm, h⟩ := hle (Submodule.mem_top : v ∈ (⊤ : Submodule E V))
  exact ⟨m, hm, h⟩

end Bl.general_b_fact_third_version
