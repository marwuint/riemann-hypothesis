import Mathlib
import GroundTheory.Brauer.SkolemNoether
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def evalQuot {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : AdjoinRoot q →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {q}) (Polynomial.aeval x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero])

theorem evalQuot_root {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : evalQuot q x hx (AdjoinRoot.root q) = x := by
  change Polynomial.aeval x Polynomial.X = x
  simp

namespace Pair

end Pair

end GlobalTheory.LKMid
