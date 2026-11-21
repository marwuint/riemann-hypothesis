import Mathlib
import Formalism.LogSumExpBounds.NuclearBound
import Formalism.LatticeRigidity.StatementD
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.Statement

open Finset MeasureTheory NumberField
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def decExp (h : ℝ) (q : ℕ) (t : ℝ) : ℝ := h / 8 * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ)))

def Ydat (n f : ℕ) (rd g b : ℝ) : ℝ := (n : ℝ) * f * rd * g * b

def epsN (c : ℝ) (n f : ℕ) : ℝ := c / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)

def dimN {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) : ℕ :=
  (∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y)
    + (∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y)
    + (∑ x, j x ^ 2) + ∑ x, 2 * j x * n0

def Vsph (i : ℕ) : ℝ := ∏ l ∈ Icc 1 i, 2 * Real.pi ^ l / ((l - 1).factorial : ℝ)

end Formalism.HermitianLatticeCounting.S7
