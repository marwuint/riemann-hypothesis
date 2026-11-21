import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators Matrix

namespace PI.KerIso.FourSqW

def qmap {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) :
    (Fin 4 → E) →ₗ[K] (Fin 4 × n → K) where
  toFun x w := ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2
  map_add' x y := by
    ext w
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext w
    simp [Finset.mul_sum, mul_left_comm]

theorem qmap_apply {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → E) (w : Fin 4 × n) :
    qmap b Q x w = ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2 := rfl

end PI.KerIso.FourSqW
