import Development.EtaleCohomology.EtaleSheaves.CorePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.CorePf2

theorem isClosedImmersion_of_cover {X Y : Scheme.{0}} (f : X ⟶ Y) {ι : Type} (O : ι → Y.Opens)
    (hcl : IsClosed (Set.range f)) (hcov : Set.range f ⊆ ⋃ i, (O i : Set Y))
    (hloc : ∀ i, IsClosedImmersion (f ∣_ O i)) : IsClosedImmersion f := by
  let O' : Option ι → Y.Opens := fun o => o.elim ⟨(Set.range f)ᶜ, hcl.isOpen_compl⟩ O
  refine IsZariskiLocalAtTarget.of_iSup_eq_top O' ?_ ?_
  · rw [eq_top_iff]
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y ∈ Set.range f
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
      exact ⟨some i, hi⟩
    · exact ⟨none, hy⟩
  · intro o
    cases o with
    | none =>
      have : IsEmpty (f ⁻¹ᵁ O' none).toScheme := ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
      infer_instance
    | some i => exact hloc i

theorem range_closed {S X₁ P : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁] (q : P ⟶ S) {V : Scheme.{0}}
    (γ : V ⟶ pullback p₁ q) : IsClosed (Set.range (γ.imageι ≫ pullback.snd p₁ q)) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact (pullback.snd p₁ q).isClosedMap _ γ.imageι.isClosedEmbedding.isClosed_range

end LateralTheory.E.CorePf2

end
