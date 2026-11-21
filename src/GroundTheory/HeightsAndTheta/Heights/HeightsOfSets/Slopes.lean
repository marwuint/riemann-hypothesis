import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HermitianLattice

namespace GroundTheory.Heights₂.Heights

open NumberField TensorProduct ComplexAt

noncomputable section

namespace HermitianBundle

variable {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K)

def gramDet (σ : K →+* ℂ) {r : ℕ} (f : Fin r → E.carrier) : ℂ :=
  Matrix.det (Matrix.of fun i j ↦ (E.metric.form σ).inner
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] f i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] f j))

def rank (F : Submodule (𝓞 K) E.carrier) : ℕ := Module.finrank (𝓞 K) F

def degreeWith (F : Submodule (𝓞 K) E.carrier) {r : ℕ} (f : Fin r → F) : ℝ :=
  Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range f))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log ‖gramDet E σ (fun i ↦ (f i : E.carrier))‖

theorem exists_linearIndependent_rank (F : Submodule (𝓞 K) E.carrier) :
    ∃ f : Fin (rank E F) → F, LinearIndependent (𝓞 K) f :=
  exists_linearIndependent_of_le_finrank le_rfl

def degree (F : Submodule (𝓞 K) E.carrier) : ℝ :=
  degreeWith E F (exists_linearIndependent_rank E F).choose

def normDegree (F : Submodule (𝓞 K) E.carrier) : ℝ := degree E F / Module.finrank ℚ K

def slope (F : Submodule (𝓞 K) E.carrier) : ℝ := normDegree E F / rank E F

def slopeMax : EReal :=
  ⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((slope E F : ℝ) : EReal)

def Saturated (F : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (a : 𝓞 K) (x : E.carrier), a ≠ 0 → a • x ∈ F → x ∈ F

end HermitianBundle

variable {K : Type*} [Field K] [NumberField K]

structure HermitianExtension (E' E E'' : HermitianBundle K) where

  incl : E'.carrier →ₗ[𝓞 K] E.carrier

  proj : E.carrier →ₗ[𝓞 K] E''.carrier
  incl_injective : Function.Injective incl
  proj_surjective : Function.Surjective proj
  exact : Function.Exact incl proj
  incl_isometric : ∀ (σ : K →+* ℂ) (x y : Fibre σ E'.carrier),
    (E.metric.form σ).inner (incl.lTensor (ComplexAt σ) x) (incl.lTensor (ComplexAt σ) y) =
      (E'.metric.form σ).inner x y
  proj_coisometric : ∀ (σ : K →+* ℂ) (x y : Fibre σ E.carrier),
    (∀ w, (E.metric.form σ).inner (incl.lTensor (ComplexAt σ) w) x = 0) →
    (∀ w, (E.metric.form σ).inner (incl.lTensor (ComplexAt σ) w) y = 0) →
    (E''.metric.form σ).inner (proj.lTensor (ComplexAt σ) x) (proj.lTensor (ComplexAt σ) y) =
      (E.metric.form σ).inner x y

end

end GroundTheory.Heights₂.Heights
