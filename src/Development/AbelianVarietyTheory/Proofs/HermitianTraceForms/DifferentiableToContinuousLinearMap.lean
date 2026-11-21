import Mathlib

namespace GlobalTheory

open Module

section Defs

variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

def isoTransvection (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) : M ≃ₗ[R] M :=
  LinearEquiv.transvection (f := b • h.flip x) (v := x) (by simp [hx])

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

theorem apply (b : R) (v : M) : isoTransvection h x hx b v = v + (b * h v x) • x := rfl

theorem coe_toLinearMap (b : R) :
    (isoTransvection h x hx b : M →ₗ[R] M) = LinearMap.transvection (b • h.flip x) x := rfl

@[simp] theorem zero : isoTransvection h x hx 0 = 1 := by
  ext v; simp [apply]

@[simp] theorem apply_self (b : R) : isoTransvection h x hx b x = x := by
  simp [apply, hx]

@[simp] theorem form_apply_self (b : R) (v : M) :
    h (isoTransvection h x hx b v) x = h v x := by
  simp [apply, hx]

@[simp] theorem form_self_apply (b : R) (v : M) :
    h x (isoTransvection h x hx b v) = h x v := by
  simp [apply, hx]

theorem apply_apply (b b' : R) (v : M) :
    isoTransvection h x hx b (isoTransvection h x hx b' v) = isoTransvection h x hx (b + b') v := by
  rw [apply, form_apply_self, apply, apply, add_mul, add_smul, add_assoc, add_comm ((b' * _) • x)]

theorem mul (b b' : R) :
    isoTransvection h x hx b * isoTransvection h x hx b' = isoTransvection h x hx (b + b') := by
  ext v; exact apply_apply h x hx b b' v

theorem inv (b : R) : (isoTransvection h x hx b)⁻¹ = isoTransvection h x hx (-b) :=
  inv_eq_of_mul_eq_one_right (by rw [mul, add_neg_cancel, zero])

theorem symm (b : R) : (isoTransvection h x hx b).symm = isoTransvection h x hx (-b) :=
  inv h x hx b

end isoTransvection

def isoTransvectionHom (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) :
    Multiplicative R →* (M ≃ₗ[R] M) where
  toFun b := isoTransvection h x hx b.toAdd
  map_one' := isoTransvection.zero h x hx
  map_mul' b b' := (isoTransvection.mul h x hx b.toAdd b'.toAdd).symm

@[simp] theorem isoTransvectionHom_apply (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
    (b : Multiplicative R) :
    isoTransvectionHom h x hx b = isoTransvection h x hx b.toAdd := rfl

theorem isoTransvectionHom_ofAdd (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) :
    isoTransvectionHom h x hx (Multiplicative.ofAdd b) = isoTransvection h x hx b := rfl

namespace isoTransvection

end isoTransvection

end Defs

namespace isoTransvection

end isoTransvection

namespace isoTransvection

end isoTransvection

section Example

private noncomputable def hyp : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u v => u.1 * star v.2 + u.2 * star v.1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

end Example

end GlobalTheory
