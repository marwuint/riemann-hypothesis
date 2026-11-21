import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

open Pointwise

theorem ine_conj_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

end GlobalTheory.NRows
