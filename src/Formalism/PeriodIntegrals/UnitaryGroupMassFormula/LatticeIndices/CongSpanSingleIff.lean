import Mathlib

noncomputable section

namespace MassDataIdxFrA

variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

def IntVec (v : ι → F) : Prop := ∀ i, v i ∈ O

def CongSpan (S : Set (ι → F)) (v : ι → F) : Prop :=
  ∃ w ∈ Submodule.span O S, ∃ z : ι → F, IntVec O z ∧ v = w + (γ : F) • z

section Mat

open Matrix

variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem congSpan_zero (S : Set (ι → F)) : CongSpan O γ S 0 := by
  exact ⟨0, zero_mem _, 0, fun _ => zero_mem _, by simp⟩

theorem congSpan_neg (S : Set (ι → F)) (v : ι → F) : CongSpan O γ S (-v) ↔ CongSpan O γ S v := by
  have key : ∀ x, CongSpan O γ S x → CongSpan O γ S (-x) := by
    rintro x ⟨w, hw, z, hz, rfl⟩
    exact ⟨-w, neg_mem hw, -z, fun i => neg_mem (hz i), by rw [smul_neg, neg_add]⟩
  exact ⟨fun h => by simpa using key _ h, key v⟩

end Mat

end MassDataIdxFrA
