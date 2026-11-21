import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FinPl.AlmostAll

theorem inv_mem_integers {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (N : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (N : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  have h2 : Valued.v (algebraMap F (Fv F v) (N : F)) = 1 := by
    rw [← h1]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (N : F)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, h2, inv_one]

theorem smul_inv_mem {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) {α : Af F} (hα : α ∈ intAf F) (h0 : ∀ w, ¬ w = v → evalV F w α = 0) :
    (N : F)⁻¹ • α ∈ intAf F ∧ ∀ w, ¬ w = v → evalV F w ((N : F)⁻¹ • α) = 0 := by
  have key : ∀ w, evalV F w ((N : F)⁻¹ • α) = algebraMap F (Fv F w) (N : F)⁻¹ * evalV F w α := by
    intro w
    rw [map_smul, Algebra.smul_def]
  have hα' : ∀ w, evalV F w α ∈ w.adicCompletionIntegers F := hα
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [key]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (inv_mem_integers hv) (hα' w)
    · rw [h0 w hw, mul_zero]
      exact zero_mem _
  · rw [key, h0 w hw, mul_zero]

theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  show ((0 : Ainf F), c • α) = c • ((0 : Ainf F), α)
  rw [Prod.smul_mk, smul_zero]

theorem tmul_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {N : ℕ} (hN : N ≠ 0) (α : Af F) (z : E) :
    pairA F 0 α ⊗ₜ[F] z = pairA F 0 ((N : F)⁻¹ • α) ⊗ₜ[F] ((N : E) * z) := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hz : (N : E) * z = (N : F) • z := by
    rw [Algebra.smul_def, map_natCast]
  rw [hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← pairA_smul, smul_smul,
    mul_inv_cancel₀ hN', one_smul]

end GlobalTheory.FinPl.AlmostAll
end
