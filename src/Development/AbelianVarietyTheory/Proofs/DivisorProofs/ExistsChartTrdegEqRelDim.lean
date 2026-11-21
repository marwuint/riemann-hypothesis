import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimGen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

open TensorProduct

theorem map_bot_eq_genericPoint {Y : Scheme.{0}} [IsIntegral Y] {A : Type} [CommRing A] [IsDomain A]
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j] :
    j (⟨⊥, inferInstance⟩ : PrimeSpectrum A) = genericPoint Y := by
  have h : genericPoint (Spec (.of A)) = (⟨⊥, inferInstance⟩ : PrimeSpectrum A) :=
    genericPoint_eq_bot_of_affine (.of A)
  rw [← h]
  exact genericPoint_eq_of_isOpenImmersion j

theorem exists_chart_trdeg_eq_relDim {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O) (W : Set Z.X) (hW : IsOpen W)
    (hη : genericPoint Z.X ∈ W) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra O A)
      (_ : Algebra.FiniteType O A) (_ : FaithfulSMul O A) (j : Spec (.of A) ⟶ Z.X)
      (_ : IsOpenImmersion j), Set.range j ⊆ W ∧
      j ≫ Z.str = Spec.map (CommRingCat.ofHom (algebraMap O A)) ∧
      Algebra.trdeg O A = Z.relDim := by
  obtain ⟨A, _, _, _, _, _, j, _, -, hj, hA⟩ :=
    exists_affine_chart_trdeg_eq Z.str (genericPoint Z.X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq Z.str (hA.symm.trans hd)
  have h₂ := topologicalKrullDim_eq_of_isEmbedding Z.gen.ι.isOpenEmbedding.isEmbedding
    (Z := Z.str ⁻¹' {genericPoint (Spec (.of O))}) (by
      rw [Scheme.Opens.range_ι, genericPoint_eq_bot_of_affine]
      ext x
      exact mem_gen_iff_eq_bot.trans ⟨fun h => PrimeSpectrum.ext h, fun h => congrArg PrimeSpectrum.asIdeal h⟩)
  rw [h₁, topologicalKrullDim_gen] at h₂
  obtain rfl : d = Z.relDim := by exact_mod_cast h₂
  obtain ⟨_, ⟨b, rfl⟩, hb, hbW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := (⟨⊥, inferInstance⟩ : PrimeSpectrum A)) (u := j ⁻¹' W)
    ((map_bot_eq_genericPoint j).symm ▸ hη : j (⟨⊥, inferInstance⟩ : PrimeSpectrum A) ∈ W) (hW.preimage j.continuous)
  have hb0 : b ≠ 0 := hb
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hb0
  have : IsDomain (Localization.Away b) := IsLocalization.isDomain_localization hle
  have : FaithfulSMul A (Localization.Away b) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic A (Localization.Away b) := IsLocalization.isAlgebraic _ (.powers b)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b)))) :=
    .of_isLocalization b
  refine ⟨Localization.Away b, inferInstance, inferInstance, inferInstance,
    .trans (S := A) inferInstance inferInstance, .trans O A _,
    Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hbW ((PrimeSpectrum.localization_away_comap_range (Localization.Away b) b).le ⟨x, rfl⟩)
  · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  · rw [trdeg_eq_of_isAlgebraic_top O A, hd]

end GlobalTheory.Vert.Model
