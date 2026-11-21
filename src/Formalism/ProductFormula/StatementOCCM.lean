import Formalism.StatementOC
import Formalism.StatementU

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.B

open Formalism

open Classical in

def AΨ (l : ℕ) (Bad : Finset ℕ) (Ψ : Finset (ZMod l)ˣ) (x : ℝ) : ℝ :=
  2 * ∑ n ∈ Icc 1 ⌊x⌋₊,
    if n.minFac ∉ Bad then
      (if h : IsUnit (n : ZMod l) then (if h.unit ∉ Ψ then Λ n * (x / n - 1) else 0) else 0)
    else 0

end Formalism.B
