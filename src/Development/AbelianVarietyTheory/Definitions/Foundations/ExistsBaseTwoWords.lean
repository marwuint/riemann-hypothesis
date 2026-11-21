import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Development.AbelianVarietyTheory.Definitions.Foundations.FoundationsPrimeFact

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseField

theorem isAlgebraic_exp (N : ℕ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simpa using isAlgebraic_one
  · exact ((Complex.isPrimitiveRoot_exp N h.ne').isIntegral h).tower_top.isAlgebraic

theorem exists_gens (E : Type) [Field E] [NumberField E] : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → ∀ (τ : E →+* ℂ) x, τ x ∈ K := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), ?_, ?_⟩
  · intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (b p.2)).algHom p.1.toRatAlgHom
  · intro K hK τ x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact K.smul_mem (hK _ (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩))

end GlobalTheory.Mem.BaseField

end
