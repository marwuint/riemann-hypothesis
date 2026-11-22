import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat

namespace CptInputs

theorem exists_constants {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} (hy : Birational y) {F : Type} [Field F] [NumberField F] (cst : F →+* Ω) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ι : F →+* F') (ψ : F' →+* Ω), ψ.comp ι = cst ∧
      ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ := by
  classical
  letI : Algebra F Ω := cst.toAlgebra
  have hle : ∀ g : MRing J, aeval y g ∈ IntermediateField.adjoin F (Set.range y) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]; exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  haveI : Algebra.EssFiniteType F Ω := by
    rw [← IntermediateField.fg_top_iff]
    refine ⟨(Set.finite_range y).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, eq_top_iff]
    intro a _
    obtain ⟨d, g, h, -, -, h0, e⟩ := hy a
    rw [eq_div_of_mul_eq h0 e.symm]
    exact div_mem (hle g) (hle h)
  let L := algebraicClosure F Ω
  haveI : FiniteDimensional F L := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType F Ω
  haveI : NumberField L := NumberField.of_module_finite F L
  refine ⟨L, inferInstance, inferInstance, algebraMap F L, algebraMap L Ω, rfl, ?_⟩
  rintro x ⟨f, hf, hx⟩
  have h1 : IsAlgebraic L x := ⟨f, hf, hx⟩
  exact ⟨⟨x, mem_algebraicClosure_iff.2 (h1.restrictScalars F)⟩, rfl⟩

end CptInputs

end GlobalTheory.CompanionTheory.Ar.Flat
