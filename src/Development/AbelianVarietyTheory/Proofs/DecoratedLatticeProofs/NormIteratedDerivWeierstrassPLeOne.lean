import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

noncomputable section

namespace GlobalTheory.Klein

variable {p : ℕ} [Fact p.Prime]

def intAt (ι : ℂ ≃+* ℂ_[p]) : Subring ℂ where
  carrier := {c | ‖ι c‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

end GlobalTheory.Klein
