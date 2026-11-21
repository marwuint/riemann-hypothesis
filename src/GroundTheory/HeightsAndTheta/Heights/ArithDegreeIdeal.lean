import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem projective_of_isTorsionFree (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.IsTorsionFree (𝓞 K) M] : Module.Projective (𝓞 K) M := by
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

instance submodule_projective {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (F : Submodule (𝓞 K) E) :
    Module.Projective (𝓞 K) F := by
  have : Module.IsTorsionFree (𝓞 K) F := inferInstance
  exact projective_of_isTorsionFree F

section Comap

variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']

def fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) : Fibre σ E' →ₗ[ℂ] Fibre σ E where
  toFun x := f.lTensor (ComplexAt σ) x
  map_add' := map_add _
  map_smul' := lTensor_complex_smul σ f

omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E'] in
theorem fibreMap_tmul (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (z : ComplexAt σ) (e : E') :
    fibreMap σ f (z ⊗ₜ e) = z ⊗ₜ f e := rfl

omit [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E'] in

theorem fibreMap_injective (σ : K →+* ℂ) {f : E' →ₗ[𝓞 K] E} (hf : Function.Injective f) :
    Function.Injective (fibreMap σ f) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf

omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E'] in

theorem conjMap_fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (x : Fibre σ E') :
    conjMap σ E (fibreMap σ f x) = fibreMap (conjugate σ) f (conjMap σ E' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

def HermitianMetric.comap (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) : HermitianMetric K E' where
  form σ := coreComap (h.form σ) (fibreMap σ f) (fibreMap_injective σ hf)
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, ← conjMap_fibreMap, ← conjMap_fibreMap, h.form_conj]

theorem HermitianMetric.comap_inner (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x y : Fibre σ E') :
    ((h.comap f hf).form σ).inner x y = (h.form σ).inner (fibreMap σ f x) (fibreMap σ f y) := rfl

end Comap

theorem HermitianBundle.degree_eq_arithDegree (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) :
    E.degree F = GroundTheory.Heights₂.Heights.arithDegree (E.metric.comap F.subtype F.injective_subtype) := by
  have hf := (HermitianBundle.exists_linearIndependent_rank E F).choose_spec
  set f := (HermitianBundle.exists_linearIndependent_rank E F).choose
  rw [arithDegree_eq _ hf (Fintype.card_fin _)]
  simp only [HermitianBundle.degree, HermitianBundle.degreeWith, degreeWith]
  congr 2
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  congr 1
  have hG : (gram ℂ fun i ↦ fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)) =
      Matrix.of fun i j ↦ (E.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f i : E.carrier)) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f j : E.carrier)) := by
    ext i j
    rfl
  have hD := (posSemidef_gram ℂ fun i ↦
    fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)).det_nonneg
  rw [hG] at hD
  simp only [GroundTheory.Heights₂.Heights.gramDet, HermitianBundle.gramDet]
  rw [hG]
  have := congrArg Complex.re (Complex.norm_of_nonneg' hD)
  simpa [f] using this

end

end GroundTheory.Heights₂.Heights
