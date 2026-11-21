import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

namespace CuspData

end CuspData

namespace Line

open GaussianInt

def planeEquiv : (GaussianInt × GaussianInt) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun v := ![v.1.re, v.1.im, v.2.re, v.2.im]
  invFun f := (⟨f 0, f 1⟩, ⟨f 2, f 3⟩)
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' n v := by
    ext i; fin_cases i <;> simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  left_inv v := by simp
  right_inv f := by ext i; fin_cases i <;> simp

theorem planeEquiv_symm_apply (f : Fin 4 → ℤ) : planeEquiv.symm f = (⟨f 0, f 1⟩, ⟨f 2, f 3⟩) := rfl

def planeForm : (GaussianInt × GaussianInt) →ₗ[ℤ] (GaussianInt × GaussianInt) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => v.1.re * w.2.re + v.1.im * w.2.im - v.2.re * w.1.re - v.2.im * w.1.im)
    (fun v v' w => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)
    (fun v w w' => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)

theorem planeForm_apply (v w : GaussianInt × GaussianInt) :
    planeForm v w = v.1.re * w.2.re + v.1.im * w.2.im - v.2.re * w.1.re - v.2.im * w.1.im := rfl

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
