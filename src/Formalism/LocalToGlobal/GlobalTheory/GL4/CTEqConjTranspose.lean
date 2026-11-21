import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsDual
import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.MultinomialPowerBound

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Matrix

section CSSpace

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end CSSpace

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
