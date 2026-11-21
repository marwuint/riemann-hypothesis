import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

noncomputable section

namespace GlobalTheory.WeilRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun i => (b i : Ω)
  have : Finite S := (Set.finite_range _).to_subtype
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff E' Ω _).mpr ⟨IntermediateField.adjoin E' S,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun σ hσ => hLU ?_⟩
  have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
  have hlin : (AlgEquiv.restrictScalarsHom E σ).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => hσ' _ (IntermediateField.subset_adjoin E' S ⟨i, rfl⟩)
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end GlobalTheory.WeilRes

end
