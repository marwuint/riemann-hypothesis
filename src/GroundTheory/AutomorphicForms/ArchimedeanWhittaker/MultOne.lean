import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Weights

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ComplexConjugate ComplexStarModule

section Schur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem eq_algebraMap_of_commute [Nontrivial V] {S : Set (V →L[ℂ] V)}
    (hirr : ∀ W : Submodule ℂ V, IsClosed (W : Set V) → (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {A : V →L[ℂ] V} (hsa : IsSelfAdjoint A) (hcomm : ∀ s ∈ S, Commute A s) :
    ∃ c : ℝ, A = algebraMap ℝ (V →L[ℂ] V) c := by
  have hnt : Nontrivial (V →L[ℂ] V) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨1, 0, fun h => hv (by simpa using congrArg (fun T : V →L[ℂ] V => T v) h)⟩⟩
  have hsub : (spectrum ℝ A).Subsingleton := by
    intro a ha b hb
    by_contra hab
    wlog hlt : a < b generalizing a b
    · exact this hb ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
    set c := (a + b) / 2 with hc
    let f : ℝ → ℝ := fun x => max (x - c) 0
    let g : ℝ → ℝ := fun x => max (c - x) 0
    have hfc : Continuous f := by fun_prop
    have hgc : Continuous g := by fun_prop
    have hgf : (fun x => g x * f x) = (0 : ℝ → ℝ) := by
      funext x
      rcases le_total x c with h | h
      · simp [f, max_eq_right (sub_nonpos.mpr h)]
      · simp [g, max_eq_right (sub_nonpos.mpr h)]
    have hQP : cfc g A * cfc f A = 0 := by
      rw [← cfc_mul g f A hgc.continuousOn hfc.continuousOn, hgf, cfc_zero]
    have hne : ∀ (φ : ℝ → ℝ), Continuous φ → ∀ x ∈ spectrum ℝ A, φ x ≠ 0 → cfc φ A ≠ 0 := by
      intro φ hφ x hx hφx h
      have hs : spectrum ℝ (cfc φ A) = φ '' spectrum ℝ A := cfc_map_spectrum φ A hsa hφ.continuousOn
      have hmem : φ x ∈ spectrum ℝ (cfc φ A) := hs ▸ ⟨x, hx, rfl⟩
      rw [h, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
      exact hφx hmem
    have hP0 : cfc f A ≠ 0 := hne f hfc b hb (by
      simp only [f]; rw [max_eq_left (by linarith)]; linarith)
    have hQ0 : cfc g A ≠ 0 := hne g hgc a ha (by
      simp only [g]; rw [max_eq_left (by linarith)]; linarith)
    have hPcomm : ∀ s ∈ S, Commute (cfc f A) s := fun s hs =>
      (hcomm s hs).cfc_real f
    set W := (LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V)).topologicalClosure with hW
    have hinv : ∀ s ∈ S, ∀ v ∈ W, s v ∈ W := by
      intro s hs v hv
      have hle : LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V) ≤
          W.comap ((s : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
        rintro _ ⟨u, rfl⟩
        simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
        have : s (cfc f A u) = cfc f A (s u) := by
          have := congrArg (fun T : V →L[ℂ] V => T u) (hPcomm s hs).eq
          simpa using this.symm
        rw [this]
        exact Submodule.le_topologicalClosure _ ⟨s u, rfl⟩
      have hcl : IsClosed ((W.comap ((s : V →L[ℂ] V) : V →ₗ[ℂ] V) : Submodule ℂ V) : Set V) :=
        (Submodule.isClosed_topologicalClosure _).preimage s.continuous
      exact Submodule.topologicalClosure_minimal _ hle hcl hv
    rcases hirr W (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
    · apply hP0
      ext v
      have : cfc f A v ∈ W := Submodule.le_topologicalClosure _ ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      simpa using this
    · apply hQ0
      have hle : LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V) ≤
          LinearMap.ker ((cfc g A : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
        rintro _ ⟨v, rfl⟩
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        have := congrArg (fun T : V →L[ℂ] V => T v) hQP
        simpa using this
      have hcl := Submodule.topologicalClosure_minimal _ hle (cfc g A).isClosed_ker
      rw [← hW, htop] at hcl
      ext v
      have : v ∈ LinearMap.ker ((cfc g A : V →L[ℂ] V) : V →ₗ[ℂ] V) := hcl Submodule.mem_top
      simpa using this
  have hne : (spectrum ℝ A).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty A hsa
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_⟩
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A hsa).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hsub hx hc
    _ = algebraMap ℝ _ c := cfc_const c A hsa

theorem eq_smul_one_of_commute [Nontrivial V] {S : Set (V →L[ℂ] V)}
    (hirr : ∀ W : Submodule ℂ V, IsClosed (W : Set V) → (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (hstar : ∀ s ∈ S, star s ∈ S) (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    {T : V →L[ℂ] V} (hT : T ∈ S) : ∃ c : ℂ, T = c • (1 : V →L[ℂ] V) := by
  have hre : ∀ s ∈ S, Commute (ℜ T : V →L[ℂ] V) s := by
    intro s hs
    rw [realPart_apply_coe]
    exact ((hcomm T hT s hs).add_left (hcomm _ (hstar T hT) s hs)).smul_left _
  have him : ∀ s ∈ S, Commute (ℑ T : V →L[ℂ] V) s := by
    intro s hs
    rw [imaginaryPart_apply_coe]
    exact (((hcomm T hT s hs).sub_left (hcomm _ (hstar T hT) s hs)).smul_left _).smul_left _
  obtain ⟨a, ha⟩ := eq_algebraMap_of_commute hirr (ℜ T).2 hre
  obtain ⟨b, hb⟩ := eq_algebraMap_of_commute hirr (ℑ T).2 him
  refine ⟨a + I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]

end Schur

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ComplexConjugate ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem topologicalClosure_span_orbit {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : UnitaryRep G H} (hρ : ρ.IsIrreducible) {x : H} (hx : x ≠ 0) :
    (Submodule.span ℂ (range fun g => ρ g x)).topologicalClosure = ⊤ := by
  set U := (Submodule.span ℂ (range fun g => ρ g x)).topologicalClosure with hU
  have hinv : ρ.IsInvariant U := by
    intro g v hv
    have hle : Submodule.span ℂ (range fun g => ρ g x) ≤ U.comap ((ρ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
      rw [← UnitaryRep.map_mul_apply]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g * h, rfl⟩)
    have hcl : IsClosed ((U.comap ((ρ g : H →L[ℂ] H) : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      (Submodule.isClosed_topologicalClosure _).preimage (ρ g).continuous
    exact Submodule.topologicalClosure_minimal _ hle hcl hv
  rcases hρ.2 U (Submodule.isClosed_topologicalClosure _) hinv with h | h
  · exfalso; apply hx
    have : x ∈ U := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, by simp⟩)
    rw [h, Submodule.mem_bot] at this
    exact this
  · exact h

theorem eq_zero_of_forall_inner_map {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : UnitaryRep G H} (hρ : ρ.IsIrreducible) {x y : H} (hx : x ≠ 0)
    (h : ∀ g, ⟪y, ρ g x⟫_ℂ = 0) : y = 0 := by
  have htop := topologicalClosure_span_orbit hρ hx
  have hle : Submodule.span ℂ (range fun g => ρ g x) ≤ (ℂ ∙ y)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h g
  have hcl := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
  rw [htop] at hcl
  have hy : y ∈ (ℂ ∙ y)ᗮ := hcl Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hy
  exact hy

variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

instance completeSpace_weightSpace (j : ℤ) : CompleteSpace (weightSpace σ j) :=
  (isClosed_weightSpace σ j).completeSpace_coe

theorem wProj_add (j : ℤ) (x y : H) : wProj σ j (x + y) = wProj σ j x + wProj σ j y := by
  simp only [wProj, map_add, smul_add]
  rw [intervalIntegral.integral_add ((continuous_wIntegrand σ j x).intervalIntegrable _ _)
    ((continuous_wIntegrand σ j y).intervalIntegrable _ _), smul_add]

theorem wProj_smul (j : ℤ) (c : ℂ) (x : H) : wProj σ j (c • x) = c • wProj σ j x := by
  simp only [wProj, map_smul, smul_comm _ c]
  rw [intervalIntegral.integral_smul, smul_comm]

noncomputable def wProjL (j : ℤ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := wProj σ j
      map_add' := wProj_add σ j
      map_smul' := wProj_smul σ j } 1 (fun x => by simpa using norm_wProj_le σ j x)

@[simp] theorem wProjL_apply (j : ℤ) (x : H) : wProjL σ j x = wProj σ j x := rfl

noncomputable def compr (j : ℤ) (g : FiltrationCocycleLiftCriterion) : weightSpace σ j →L[ℂ] weightSpace σ j :=
  ((wProjL σ j).comp ((σ g).comp (weightSpace σ j).subtypeL)).codRestrict (weightSpace σ j)
    (fun x => wProj_mem σ j _)

@[simp] theorem coe_compr_apply (j : ℤ) (g : FiltrationCocycleLiftCriterion) (v : weightSpace σ j) :
    ((compr σ j g v : weightSpace σ j) : H) = wProj σ j (σ g v) := rfl

end GroundTheory.Automorphic.ArchWhittaker
