import Mathlib

namespace GroundTheory.Arith.Toric

open Module PointedCone

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

def exposedFace (σ : PointedCone 𝕜 V) (u : Dual 𝕜 V) : PointedCone 𝕜 V :=
  σ ⊓ ofSubmodule (LinearMap.ker (u : V →ₗ[𝕜] 𝕜))

@[simp] theorem mem_exposedFace {σ : PointedCone 𝕜 V} {u : Dual 𝕜 V} {x : V} :
    x ∈ exposedFace σ u ↔ x ∈ σ ∧ u x = 0 := by
  simp [exposedFace]

def dualFace (σ τ : PointedCone 𝕜 V) : PointedCone 𝕜 (Dual 𝕜 V) where
  carrier := {u | (∀ x ∈ σ, 0 ≤ u x) ∧ ∀ x ∈ τ, u x = 0}
  add_mem' := fun {u v} hu hv =>
    ⟨fun x hx => by simpa using add_nonneg (hu.1 x hx) (hv.1 x hx),
      fun x hx => by simp [hu.2 x hx, hv.2 x hx]⟩
  zero_mem' := ⟨fun _ _ => le_rfl, fun _ _ => rfl⟩
  smul_mem' := fun c u hu =>
    ⟨fun x hx => by
        have e : (c • u) x = (c : 𝕜) * u x := rfl
        rw [e]
        exact mul_nonneg c.2 (hu.1 x hx),
      fun x hx => by
        have e : (c • u) x = (c : 𝕜) * u x := rfl
        rw [e, hu.2 x hx, mul_zero]⟩

@[simp] theorem mem_dualFace {σ τ : PointedCone 𝕜 V} {u : Dual 𝕜 V} :
    u ∈ dualFace σ τ ↔ (∀ x ∈ σ, 0 ≤ u x) ∧ ∀ x ∈ τ, u x = 0 := Iff.rfl

def predualFace (σ : PointedCone 𝕜 V) (ν : PointedCone 𝕜 (Dual 𝕜 V)) : PointedCone 𝕜 V where
  carrier := {x | x ∈ σ ∧ ∀ u ∈ ν, u x = 0}
  add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun u hu => by simp [hx.2 u hu, hy.2 u hu]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => map_zero _⟩
  smul_mem' := fun c x hx =>
    ⟨Submodule.smul_mem _ c hx.1, fun u hu => by
      have e : u (c • x) = (c : 𝕜) * u x := by
        change u ((c : 𝕜) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [e, hx.2 u hu, mul_zero]⟩

@[simp] theorem mem_predualFace {σ : PointedCone 𝕜 V} {ν : PointedCone 𝕜 (Dual 𝕜 V)} {x : V} :
    x ∈ predualFace σ ν ↔ x ∈ σ ∧ ∀ u ∈ ν, u x = 0 := Iff.rfl

end GroundTheory.Arith.Toric
