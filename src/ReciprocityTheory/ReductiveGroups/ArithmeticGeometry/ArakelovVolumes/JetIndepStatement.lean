import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR

def multiLt (D a : ℕ) : Finset (Fin D → ℕ) :=
  (Finset.range a).biUnion (fun d => Finset.Nat.antidiagonalTuple D d)

end ReciprocityTheory.ChartRestriction.G.AR
