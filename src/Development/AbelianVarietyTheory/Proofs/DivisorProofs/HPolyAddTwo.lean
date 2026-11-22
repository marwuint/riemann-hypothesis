import Mathlib

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial

namespace GlobalTheory.FibLine

def hPoly (k : ℕ) : MvPolynomial (Fin 2) ℂ :=
  (Nat.rec (motive := fun _ => MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ) (1, X 0)
    (fun _ p => (p.2, X 0 * p.2 - X 1 * p.1)) k).1

end GlobalTheory.FibLine
