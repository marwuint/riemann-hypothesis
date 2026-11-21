import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolution

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

section WeakAdjLemmas

variable {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem WeakAdj.sub {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f - f') (w - w') := by
  intro g
  rw [inner_sub_right, inner_sub_right, h g, h' g]

end WeakAdjLemmas

theorem split (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    SplitStatement E H₁ H₂ := by
  intro ι t K hK hrange f w hfw
  haveI : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := K.exists_add_mem_mem_orthogonal f
  have h2 : WeakAdj ι t f₂ 0 := by
    intro g
    rw [inner_zero_right]
    exact Submodule.inner_right_of_mem_orthogonal (hrange (LinearMap.mem_range_self t g)) hf₂
  refine ⟨f₁, f₂, rfl, hf₁, hf₂, ?_, h2⟩
  have h1 := hfw.sub h2
  simpa using h1

end ReciprocityTheory.L2DbarEstimates
