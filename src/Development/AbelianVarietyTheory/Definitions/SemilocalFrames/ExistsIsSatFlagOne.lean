import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.SatModel

open Formalism.MainNotions.S GlobalTheory.Count

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  have := Real.pi_pos
  refine mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem cIw_pos (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 < cIw p q j := by
  unfold cIw
  have := volU_pos
  refine div_pos (mul_pos (by positivity) (mul_pos (this _) (this _)))
    (mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (this _) (by positivity)) (this _)) (this _))

end GlobalTheory.FlagMeas.SatModel
