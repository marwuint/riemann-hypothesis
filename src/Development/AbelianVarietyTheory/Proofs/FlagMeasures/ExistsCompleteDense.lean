import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.HilbTensorExists

theorem exists_pre_fin (n : ℕ) : ∀ (H : Fin n → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)],
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  induction n with
  | zero =>
    intro H _ _
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 1, fun x y => ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  | succ n ih =>
    intro H _ _
    obtain ⟨K, iK, iK', t, ht⟩ := ih (fun i => H i.castSucc)
    refine ⟨K ⊗[ℂ] H (Fin.last n), inferInstance, inferInstance,
      fun x => t (fun i => x i.castSucc) ⊗ₜ[ℂ] x (Fin.last n), fun x y => ?_⟩
    rw [TensorProduct.inner_tmul, ht, Fin.prod_univ_castSucc]

theorem exists_pre {ι : Type} [Fintype ι] (H : ι → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  let e := Fintype.equivFin ι
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre_fin (Fintype.card ι) (fun i => H (e.symm i))
  refine ⟨K, iK, iK', fun x => t (fun i => x (e.symm i)), fun x y => ?_⟩
  rw [ht]
  exact e.symm.prod_comp (fun v => ⟪x v, y v⟫_ℂ)

theorem exists_complete_dense {X K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : X → K) :
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : CompleteSpace L) (s : X → L),
      (∀ x y, ⟪s x, s y⟫_ℂ = ⟪t x, t y⟫_ℂ) ∧ Dense (Submodule.span ℂ (Set.range s) : Set L) := by
  let V := Submodule.span ℂ (Set.range t)
  let u : X → V := fun x => ⟨t x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    rfl
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    fun x => ((u x : V) : UniformSpace.Completion V), fun x y => ?_, ?_⟩
  · rw [UniformSpace.Completion.inner_coe]
    rfl
  · refine UniformSpace.Completion.denseRange_coe.mono ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ (Set.range u) := hu ▸ Submodule.mem_top
    have hm := Submodule.mem_map_of_mem
      (f := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap) hv
    rw [Submodule.map_span, ← Set.range_comp] at hm
    exact hm

end GlobalTheory.HilbTensorExists
