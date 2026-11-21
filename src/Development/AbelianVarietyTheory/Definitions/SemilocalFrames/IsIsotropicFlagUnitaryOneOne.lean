import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.Model

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def e2 : Fin 2 → Bool := ![true, false]

def mU : Formalism.REAL.UJ e2 :=
  ⟨⟨!![5 / 4, 3 / 4; 3 / 4, 5 / 4], !![5 / 4, -3 / 4; -3 / 4, 5 / 4],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num⟩, by
    change Formalism.REAL.inUJ e2 !![5 / 4, 3 / 4; 3 / 4, 5 / 4]
    unfold Formalism.REAL.inUJ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.REAL.Jm, e2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        map_ofNat] <;> norm_num⟩

end GlobalTheory.FlagMeas.Model
