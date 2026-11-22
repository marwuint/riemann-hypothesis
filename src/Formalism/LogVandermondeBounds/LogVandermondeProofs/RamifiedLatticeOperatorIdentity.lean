import Formalism.LogVandermondeBounds.FinrankFiberSumZero

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section SlopeTestRemainingChoices

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

lemma pair_add_left (f g x : Fin r → k) : pair (f + g) x = pair f x + pair g x := by
  simp [pair, add_mul, Finset.sum_add_distrib]

def pairL (x : Fin r → k) : (Fin r → k) →+ k where
  toFun f := pair f x
  map_zero' := by simp [pair]
  map_add' f g := pair_add_left f g x

lemma pairL_apply (x f : Fin r → k) : pairL x f = pair f x := rfl

end SlopeTestRemainingChoices

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
