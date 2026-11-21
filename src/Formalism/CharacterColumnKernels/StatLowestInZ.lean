import Mathlib

open Finset Classical

noncomputable section

namespace Formalism.NG

def blockSum {Ir ι : Type*} (tw : ℤ → Ir → Ir) (I : Finset ι) (rp : ι → Multiset Ir) (dd : ι → ℕ) :
    Multiset Ir :=
  ∑ i ∈ I, ∑ k ∈ range (dd i), (rp i).map (tw ((dd i : ℤ) - 1 - 2 * k))

end Formalism.NG
