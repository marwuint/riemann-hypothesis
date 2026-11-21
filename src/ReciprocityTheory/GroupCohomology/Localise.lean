import ReciprocityTheory.GroupCohomology.LocaliseA

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  refine isLocalized_of_cx j.hom t ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g

end ReciprocityTheory.Coh
