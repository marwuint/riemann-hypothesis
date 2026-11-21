import Mathlib
import Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivAddOne

open Polynomial

namespace GlobalTheory.FixedRoots

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

end GlobalTheory.FixedRoots
