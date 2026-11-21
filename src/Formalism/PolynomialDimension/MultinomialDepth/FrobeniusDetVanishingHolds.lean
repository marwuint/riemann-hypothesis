import Formalism.PolynomialDimension.FrameSum

noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Formalism.CountingSumsFrames

lemma frob_row {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p] {k : ℕ}
    (h : Matrix (Fin k) (Fin k) F) (a s : ℕ) (ha : a ≤ s) (t : Fin k → F) (c : Fin k) :
    ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
      ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c := by
  haveI : ExpChar F p := ExpChar.prime (Fact.out)
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le ha]

end Formalism.CountingSumsFrames
