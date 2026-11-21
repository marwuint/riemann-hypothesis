import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace UpperTheory.V.Af

theorem continuous_restrictScalarsHom (F E Ω : Type) [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] : Continuous (AlgEquiv.restrictScalarsHom F : G E Ω →* G F Ω) := by
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis F M
  set t : Set Ω := Set.range (fun i => ((b i : M) : Ω)) with ht_def
  have hMt : M ≤ IntermediateField.adjoin F t := by
    intro m hm
    have h := congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨m, hm⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    rw [← h]
    exact sum_mem fun i _ => IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin F t (Set.mem_range_self i))
  have hint : ∀ x ∈ t, IsIntegral E x := by
    rintro x ⟨i, rfl⟩
    have : IsIntegral F (b i) := IsIntegral.of_finite F _
    exact (IsIntegral.map (IsScalarTower.toAlgHom F M Ω) this).tower_top
  haveI : Finite t := Set.finite_range _
  haveI : FiniteDimensional E (IntermediateField.adjoin E t) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin E t, inferInstance, fun σ hσ => hMs ?_⟩
  have hH : IntermediateField.adjoin F t ≤ IntermediateField.fixedField
      (Subgroup.map (AlgEquiv.restrictScalarsHom F (A := Ω) (S := E))
        (IntermediateField.adjoin E t).fixingSubgroup) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro f ⟨τ, hτ, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      (IntermediateField.subset_adjoin E _ hx)
  exact IntermediateField.fixingSubgroup_antitone hMt
    ((IntermediateField.le_iff_le _ _).1 hH ⟨σ, hσ, rfl⟩)

theorem surjective_algebraMap_real (K : Type) [Field K] [NumberField K] [IsCMField K] (h : Module.finrank ℚ K = 2) :
    Function.Surjective (algebraMap ℚ (maximalRealSubfield K)) := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
  rw [h, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h1
  have h2 : Module.finrank ℚ (maximalRealSubfield K) = 1 := by omega
  exact ((Algebra.finrank_eq_one_iff_bijective_algebraMap).1 h2).2

end UpperTheory.V.Af
