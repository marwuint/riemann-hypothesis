import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

namespace Line

open GaussianInt

def planeForm : (GaussianInt × GaussianInt) →ₗ[ℤ] (GaussianInt × GaussianInt) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => v.1.re * w.2.re + v.1.im * w.2.im - v.2.re * w.1.re - v.2.im * w.1.im)
    (fun v v' w => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)
    (fun v w w' => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)

theorem planeForm_apply (v w : GaussianInt × GaussianInt) :
    planeForm v w = v.1.re * w.2.re + v.1.im * w.2.im - v.2.re * w.1.re - v.2.im * w.1.im := rfl

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
