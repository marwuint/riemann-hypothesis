import ReciprocityTheory.Chebotarev.Ucoord

open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem mem_latOf {I : Ideal (𝓞 E)} {x : mixedSpace E} : x ∈ latOf I ↔ ∃ α ∈ I, embZ α = x := by
  simp only [latOf, Submodule.mem_map, Submodule.restrictScalars_mem]

scoped instance discreteTopology_latOf (I : Ideal (𝓞 E)) : DiscreteTopology (latOf I) := by
  have hsub : ((latOf I : Set (mixedSpace E))) ⊆ (mixedEmbedding.integerLattice E : Set _) := by
    intro x hx
    obtain ⟨α, -, rfl⟩ := mem_latOf.mp hx
    exact ⟨α, rfl⟩
  exact DiscreteTopology.of_subset (inferInstance : DiscreteTopology (mixedEmbedding.integerLattice E)) hsub

end ReciprocityTheory.Cheb
