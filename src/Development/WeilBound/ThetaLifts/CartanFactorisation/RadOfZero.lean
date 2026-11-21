import Development.WeilBound.ThetaLifts.CartanFactorisation.SpanOrbitStab
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKF

open scoped InnerProductSpace
open Abs

section

variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)

theorem rad_of_zero (hs : ∀ x y, β x y = starRingEnd ℂ (β y x)) (hp : ∀ x, 0 ≤ (β x x).re) {x : Q} (h : β x x = 0) :
    β x = 0 := by
  let c : PreInnerProductSpace.Core ℂ Q :=
    { inner := fun x y => β x y
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := hp
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  ext y
  have := InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  change ‖β x y‖ * ‖β y x‖ ≤ RCLike.re (β x x) * RCLike.re (β y y) at this
  rw [h, map_zero, zero_mul, hs y x, RCLike.norm_conj] at this
  have h2 : ‖β x y‖ = 0 := by nlinarith [norm_nonneg (β x y)]
  simpa using h2

def QR : Type := Q ⧸ LinearMap.ker β

instance : AddCommGroup (QR β) := inferInstanceAs (AddCommGroup (Q ⧸ LinearMap.ker β))
instance : Module ℂ (QR β) := inferInstanceAs (Module ℂ (Q ⧸ LinearMap.ker β))

end

end PositivityTheory.ThKF

end
