import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem mul_triv_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b h x : S) (t d : A)
    (hx : x * b * (σ x).unop = algebraMap A S t) (hh : h * (σ h).unop = algebraMap A S d) :
    h * x * b * (σ (h * x)).unop = algebraMap A S (t * d) := by
  calc h * x * b * (σ (h * x)).unop = h * (x * b * (σ x).unop) * (σ h).unop := by
        simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S t * (h * (σ h).unop) := by rw [hx, ← Algebra.commutes, mul_assoc]
    _ = _ := by rw [hh, map_mul]

end GlobalTheory.LKMid
