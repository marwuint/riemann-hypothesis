import Mathlib
import GroundTheory.AutomorphicForms.HermitianOrthogonal

noncomputable section

namespace GroundTheory.Automorphic

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]

theorem bijective_of_injective_sesq [FiniteDimensional E V]
    (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (hB : Function.Injective B) : Function.Bijective B := by
  set b := Module.finBasis E V
  set G := gram B b
  let sx : (Fin (finrank E V) → E) → V := fun c => b.equivFun.symm (fun i => conj F E (c i))
  have key : ∀ c j, B (sx c) (b j) = Matrix.vecMul c G j := by
    intro c j
    simp only [sx, Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ₂, conjHom_apply,
      conj_conj, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.vecMul,
      dotProduct, G, gram_apply]
  have hinj : Function.Injective (Matrix.vecMulLinear G) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : B (sx c) = 0 := b.ext fun j => by
      rw [key, LinearMap.zero_apply]
      exact congrFun hc j
    have h2 : sx c = 0 := hB (by rw [h1, map_zero])
    funext i
    have h3 := congrArg (fun v => b.equivFun v i) h2
    simp only [sx, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] at h3
    rw [← conj_conj (F := F) (c i), h3, map_zero, Pi.zero_apply]
  refine ⟨hB, fun f => ?_⟩
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.1 hinj (fun j => f (b j))
  refine ⟨sx c, b.ext fun j => ?_⟩
  rw [key]
  exact congrFun hc j

namespace HermitianForm

def quasiReflection (h : HermitianForm F E V) (w : V) (c : E) : V →ₗ[E] V :=
  LinearMap.id - (c • h.toSesq w).smulRight w

def equivOfIsometry [FiniteDimensional E V] (h : HermitianForm F E V) (f : V →ₗ[E] V)
    (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) : V ≃ₗ[E] V :=
  LinearEquiv.ofInjectiveEndo f (by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply h.eq_zero_of_forall
    intro y
    rw [← hf, hx, map_zero, LinearMap.zero_apply])

@[simp]
theorem equivOfIsometry_apply [FiniteDimensional E V] (h : HermitianForm F E V) (f : V →ₗ[E] V)
    (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) (x : V) :
    h.equivOfIsometry f hf x = f x := rfl

def orthogonal (h : HermitianForm F E V) (U : Submodule E V) : Submodule E V where
  carrier := {y | ∀ x ∈ U, h.toSesq x y = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := map_zero _
  smul_mem' c y hy x hx := by rw [h.toSesq_smul_right, hy x hx, mul_zero]

theorem mem_orthogonal (h : HermitianForm F E V) (U : Submodule E V) (y : V) :
    y ∈ h.orthogonal U ↔ ∀ x ∈ U, h.toSesq x y = 0 := Iff.rfl

end HermitianForm

end GroundTheory.Automorphic

end
