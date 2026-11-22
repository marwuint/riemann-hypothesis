import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HermitianEuclidean

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section SMul

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

theorem fibre_smul_eq (a : ComplexAt σ) (x : Fibre σ E) :
    a • x = (ofComplex σ).symm a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | tmul z e => rw [smul_tmul', smul_tmul', complex_smul_def, smul_eq_mul]; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

instance (F : Type*) [AddCommGroup F] [Module (𝓞 K) F] :
    CompatibleSMul ℂ (ComplexAt σ) (Fibre σ E) (Fibre σ F) where
  smul_tmul a x y := by
    rw [fibre_smul_eq, fibre_smul_eq σ F, TensorProduct.smul_tmul]

instance (F : Type*) [AddCommGroup F] [Module (𝓞 K) F] :
    CompatibleSMul (ComplexAt σ) ℂ (Fibre σ E) (Fibre σ F) where
  smul_tmul c x y := by
    rw [show c • x = (ofComplex σ c) • x from (fibre_smul_eq σ E _ x).symm,
      show c • y = (ofComplex σ c) • y from (fibre_smul_eq σ F _ y).symm, TensorProduct.smul_tmul]

end SMul

variable [NumberField K]

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

def FibreSpace (_h : HermitianMetric K E) (σ : K →+* ℂ) : Type _ := Fibre σ E

namespace FibreSpace

variable (h : HermitianMetric K E) (σ : K →+* ℂ)

instance : AddCommGroup (FibreSpace h σ) := inferInstanceAs (AddCommGroup (Fibre σ E))

instance : Module ℂ (FibreSpace h σ) := inferInstanceAs (Module ℂ (Fibre σ E))

instance : NormedAddCommGroup (FibreSpace h σ) :=
  letI : InnerProductSpace.Core ℂ (FibreSpace h σ) := h.form σ
  this.toNormedAddCommGroup

instance : InnerProductSpace ℂ (FibreSpace h σ) := InnerProductSpace.ofCore _

def equiv : Fibre σ E ≃ₗ[ℂ] FibreSpace h σ := LinearEquiv.refl ℂ _

theorem inner_equiv (x y : Fibre σ E) :
    inner ℂ (equiv h σ x) (equiv h σ y) = (h.form σ).inner x y := rfl

end FibreSpace

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]

def tensorCoord (hE : HermitianMetric K E) (hF : HermitianMetric K F) (σ : K →+* ℂ) :
    Fibre σ (E ⊗[𝓞 K] F) ≃ₗ[ℂ] FibreSpace hE σ ⊗[ℂ] FibreSpace hF σ :=
  ((AlgebraTensorModule.distribBaseChange (𝓞 K) (ComplexAt σ) E F).restrictScalars ℂ).trans
    ((equivOfCompatibleSMul ℂ (ComplexAt σ) ℂ (Fibre σ E) (Fibre σ F)).trans
      (TensorProduct.congr (FibreSpace.equiv hE σ) (FibreSpace.equiv hF σ)))

variable (hE : HermitianMetric K E) (hF : HermitianMetric K F)

end

end GroundTheory.Heights₂.Heights
