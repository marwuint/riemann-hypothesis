import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem continuous_adelicChar_neg_supSum :
    Continuous fun X : Pos n → 𝔸[K] => (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def HasContRep (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (F : normOneGL K n → ℂ) : Prop :=
  Continuous F ∧ (∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y) ∧ (fun y => φ (mk Γ₁ y)) =ᵐ[μ] F

variable {μ}

theorem HasContRep.unique {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) (h' : HasContRep μ φ F') : F = F' :=
  (h.1.ae_eq_iff_eq μ h'.1).1 (h.2.2.symm.trans h'.2.2)

theorem HasContRep.add {φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) (h' : HasContRep μ ψ F') : HasContRep μ (φ + ψ) (F + F') := by
  refine ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_add φ ψ), h.2.2, h'.2.2]
    with y h1 h2 h3
  simp only [Function.comp_apply, Pi.add_apply] at h1
  rw [h1, h2, h3, Pi.add_apply]

theorem HasContRep.smul (c : ℂ) {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) : HasContRep μ (c • φ) (c • F) := by
  refine ⟨h.1.const_smul c, fun γ hγ y => by simp [h.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_smul c φ), h.2.2]
    with y h1 h2
  simp only [Function.comp_apply, Pi.smul_apply] at h1
  rw [h1, h2, Pi.smul_apply]

variable (μ) in

theorem hasContRep_rconv (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    HasContRep μ ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ)
      (rconv Γ₁ μ f φ) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine ⟨continuous_rconv Γ₁ μ f φ, fun γ hγ y => rconv_mul_left Γ₁ μ f φ hγ y, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (integrated_ae_eq_rconvQ Γ₁ μ f φ)]
    with y hy
  simp only [Function.comp_apply] at hy
  rw [hy, rconvQ_mk]

theorem HasContRep.translate {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) (x : normOneGL K n) :
    HasContRep μ (rightRegularRep Γ₁ μ x φ) (fun y => F (y * x)) := by
  refine ⟨h.1.comp (continuous_mul_const x), fun γ hγ y => by
    show F (γ * y * x) = F (y * x)
    rw [mul_assoc, h.2.1 γ hγ], ?_⟩
  have h2 : (fun y => φ (mk Γ₁ (y * x))) =ᵐ[μ] fun y => F (y * x) :=
    (measurePreserving_mul_right μ x).quasiMeasurePreserving.ae_eq_comp h.2.2
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (coeFn_rightRegularRep Γ₁ μ x φ), h2]
    with y h1 h3
  simp only [Function.comp_apply] at h1
  rw [h1, rightMul_mk, h3]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ) in

def smoothSpan (σ : UnitaryRep (normOneGL K n) H) : Submodule ℂ H :=
  Submodule.span ℂ {w | ∃ (x : normOneGL K n) (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (v : H), IsSmoothTest f ∧ w = σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)}

end MultiplicityOne

end

end GroundTheory.Automorphic
