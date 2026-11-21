import Mathlib

set_option autoImplicit false

namespace GordanCones

def toQ {n : ℕ} (v : Fin n → ℤ) : Fin n → ℚ := fun i => (v i : ℚ)

end GordanCones
