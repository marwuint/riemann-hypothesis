import Mathlib

namespace Formalism.RankGapBounds.JumpSetsAlt

open Finset

def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l

def posPairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

def eExp {N : ℕ} (U : Fin N → ℤ) (l : ℕ) : ℕ :=
  ∑ p ∈ posPairs N, maxVal l (U p.1 - U p.2 - 1).toNat

end Formalism.RankGapBounds.JumpSetsAlt
