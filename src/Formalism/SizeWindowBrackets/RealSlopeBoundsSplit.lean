import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold

namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas

open Finset

noncomputable section

def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ :=
  (∑ u, d u * X u) / ∑ u, d u

def sF {ι : Type*} [Fintype ι] (d muN h : ι → ℝ) : ℝ :=
  wmean d (fun u => muN u - h u)

end

end Formalism.LFunctionChainParameters.WeightedMeanLemmas
