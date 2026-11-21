import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemKFinOfIsLocallyConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantLinOm

noncomputable section

open GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace GlobalTheory.LocSW.Lin

section Alg

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] {c : A →ₐ[k] A} {δ : A} {β ν κ : Type} [Fintype β]
  [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ] {JB : Matrix β β A} [Invertible (2 : k)]

variable (c JB) in

def trB : LinearMap.BilinForm k (β → A) :=
  LinearMap.mk₂ k (fun u v => -Algebra.trace k A (u ⬝ᵥ JB *ᵥ fun i => c (v i)))
    (fun u u' v => by rw [add_dotProduct, map_add, neg_add])
    (fun a u v => by rw [smul_dotProduct, map_smul, smul_neg])
    (fun u v v' => by
      rw [← neg_add, ← map_add, ← dotProduct_add, ← mulVec_add]; congr 4; funext i; simp)
    (fun a u v => by
      rw [smul_neg, ← map_smul, ← dotProduct_smul, ← mulVec_smul]; congr 4; funext i; simp)

omit [DecidableEq β] [Invertible (2 : k)] in

theorem trB_apply (u v : β → A) : trB c JB u v = -Algebra.trace k A (u ⬝ᵥ JB *ᵥ fun i => c (v i)) := rfl

def actC (e : (β → A) ≃ₗ[k] (κ → k)) (g : GL β A) : (κ → k) →ₗ[k] (κ → k) :=
  e.toLinearMap ∘ₗ (Matrix.toLin' g.val).restrictScalars k ∘ₗ e.symm.toLinearMap

omit [Fintype κ] [Invertible (2 : k)]

theorem actC_actC (e : (β → A) ≃ₗ[k] (κ → k)) (g g' : GL β A) (x : κ → k) :
    actC e g (actC e g' x) = actC e (g * g') x := by simp [actC]

theorem actC_one (e : (β → A) ≃ₗ[k] (κ → k)) (x : κ → k) : actC e 1 x = x := by simp [actC]

variable (c JB) in

def linOm (e : (β → A) ≃ₗ[k] (κ → k)) : UG c JB →* Module.End ℂ ((κ → k) → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ (actC e (h : GL β A)⁻¹)
  map_one' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_one]
  map_mul' h h' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_actC]

theorem linOm_apply (e : (β → A) ≃ₗ[k] (κ → k)) (h : UG c JB) (φ : (κ → k) → ℂ) (x : κ → k) :
    linOm c JB e h φ x = φ (actC e (h : GL β A)⁻¹ x) := rfl

end Alg

open scoped TensorProduct
end GlobalTheory.LocSW.Lin

end
