import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers

noncomputable section

namespace GlobalTheory.EX.DQ.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB NumberField

section Lat

variable {O L V : Type} [CommRing O] [Field L] [NumberField L] [AddCommGroup V] [Module ℂ V] {φ : O →+* ℂ}

open Classical in

def sat (σ : L →+* ℂ) (M : Rows.OLat O φ V) : Rows.OLat O φ V where
  gen := (Finset.univ ×ˢ M.gen).image fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2
  span_top := by
    rw [eq_top_iff, ← M.span_top, Submodule.span_le]
    intro v hv
    obtain ⟨i⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 L)) := (RingOfIntegers.basis L).index_nonempty
    have h0 : σ (RingOfIntegers.basis L i : L) ≠ 0 := by
      rw [map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
      exact (RingOfIntegers.basis L).ne_zero i
    have := Submodule.smul_mem (Submodule.span ℂ (((Finset.univ ×ˢ M.gen).image
      fun p => σ (RingOfIntegers.basis L p.1 : L) • p.2 : Finset V) : Set V)) (σ (RingOfIntegers.basis L i : L))⁻¹
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, v), by simpa using hv, rfl⟩)))
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this

end Lat

end GlobalTheory.EX.DQ.Model

end
