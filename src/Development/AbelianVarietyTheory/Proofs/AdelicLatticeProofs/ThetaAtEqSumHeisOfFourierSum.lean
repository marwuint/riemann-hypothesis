import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isSBHalf_halfInd {D : D7} {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) :
    IsSBHalf e Λ (halfInd e Λ) := by
  classical
  refine ⟨fun t ht => ?_, 1, one_pos, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by simp [halfInd, h])
  · have : (t + 1 • u ∈ Λ ∧ IsHalf e (t + 1 • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
      rw [one_smul, Λ.add_mem_cancel_right hu]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    simp only [halfInd, this]
  · by_contra h
    rw [one_smul] at h
    exact ht (by simp [halfInd, h])

end GlobalTheory
