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

theorem fieldCoord_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (x : K) :
    fieldCoord σ (z ⊗ₜ x) = (ofComplex σ).symm z * σ x :=
  rfl

def fieldStdCoord (σ : K →+* ℂ) (n : ℕ) : Fibre σ (Fin n → K) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i ↦ fieldCoord σ ∘ₗ LinearMap.proj i) ∘ₗ
      ((piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) fun _ : Fin n ↦ K).restrictScalars ℂ).toLinearMap

theorem fieldStdCoord_apply (σ : K →+* ℂ) (n : ℕ) (x : Fibre σ (Fin n → K)) (i : Fin n) :
    fieldStdCoord σ n x i = fieldCoord σ (piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ)
      (fun _ : Fin n ↦ K) x i) :=
  rfl

end

end GroundTheory.Heights₂.Heights
