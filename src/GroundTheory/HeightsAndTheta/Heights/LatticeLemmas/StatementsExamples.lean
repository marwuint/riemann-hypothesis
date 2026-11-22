import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def embLinear (σ : K →+* ℂ) : K →ₗ[𝓞 K] ComplexAt σ where
  toFun x := ofComplex σ (σ x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    rw [RingHom.id_apply, smul_def, Algebra.smul_def, map_mul, map_mul]

def fieldCoord (σ : K →+* ℂ) : Fibre σ K →ₗ[ℂ] ℂ :=
  (ofComplex σ).symm.toLinearEquiv.toLinearMap ∘ₗ
    ((embLinear σ).liftBaseChange (ComplexAt σ)).restrictScalars ℂ

end

end GroundTheory.Heights₂.Heights
