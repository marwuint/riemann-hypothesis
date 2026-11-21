import Mathlib

namespace UpperTheory.Reformulated.B.Qh27

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

theorem smooth_on_group_sum.{u_1} :
    ∀ {n : ℕ} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ),
      (∀ i ∈ s, SmoothOnG ε (f i)) → SmoothOnG ε (fun x ↦ ∑ i ∈ s, f i x) := by
  intro n ε ι s f h g₀ hg₀
  choose! U F hU hmem hF heq using fun i hi ↦ h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x ↦ ∑ i ∈ s, F i x, isOpen_biInter_finset hU,
    Set.mem_iInter₂.2 hmem, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi ↦ (hF i hi).mono (Set.biInter_subset_of_mem (Finset.mem_coe.2 hi))
  · intro g hg hgu
    exact Finset.sum_congr rfl fun i hi ↦ heq i hi g (Set.mem_iInter₂.1 hg i hi) hgu

end UpperTheory.Reformulated.B.Qh27
