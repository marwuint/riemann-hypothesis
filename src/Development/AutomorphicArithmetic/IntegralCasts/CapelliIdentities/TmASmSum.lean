import Mathlib

namespace UpperTheory.Reformulated.B.Qf26

open scoped ContDiff Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε ↦ Matrix.diagonal fun a ↦ if ε a then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {_} ε g ↦ gᴴ * Jm ε * g = Jm ε

noncomputable def SmoothOnG :
    {n : ℕ} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop :=
  fun {n} ε f ↦
    ∀ g₀ : Matrix (Fin n) (Fin n) ℂ, inUJ ε g₀ →
      ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
        IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g

theorem tmA_sm_sum.{u_1} :
    ∀ {n : ℕ} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ),
      (∀ i ∈ s, SmoothOnG ε (F i)) → SmoothOnG ε (fun x ↦ ∑ i ∈ s, F i x) := by
  intro n ε ι s F h g₀ hg
  classical
  choose! U G hUo hUm hG hE using fun i hi => h i hi g₀ hg
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, G i x, isOpen_biInter_finset hUo, ?_, ?_, ?_⟩
  · exact Set.mem_iInter₂.2 hUm
  · exact ContDiffOn.sum fun i hi => (hG i hi).mono (Set.biInter_subset_of_mem hi)
  · intro g hgU hgJ
    exact Finset.sum_congr rfl fun i hi => hE i hi g (Set.mem_iInter₂.1 hgU i hi) hgJ

end UpperTheory.Reformulated.B.Qf26
