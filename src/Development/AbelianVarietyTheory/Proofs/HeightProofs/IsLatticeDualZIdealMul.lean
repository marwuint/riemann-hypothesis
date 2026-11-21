import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CuspFormNormData

open NumberField Matrix Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents GlobalTheory.IndefiniteRowSideFullHecke.CuspFormFieldDegree

namespace GlobalTheory.CuspCharLattice

variable {R : Ranks} {H : Host R} {n : ℕ}

theorem host_AA_ne_zero (H : Host R) : H.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact H.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := H.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

end GlobalTheory.CuspCharLattice
