import Formalism.PeriodIntegrals.SqfLab
import Mathlib

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

def monicDeg (g d : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  Finset.univ.image (fun c : Fin d → ZMod g => X ^ d + ∑ i, C (c i) * X ^ (i : ℕ))

open Classical in

def irrDeg (g d : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  (monicDeg g d).filter Irreducible

end PI.SqfPrimeFactor.W
