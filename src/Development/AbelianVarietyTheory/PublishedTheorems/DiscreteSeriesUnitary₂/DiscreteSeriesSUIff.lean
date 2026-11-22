import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

namespace GlobalTheory.Published

open GlobalTheory.DSSU

def DiscreteSeriesSU : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ε : Fin n → Bool, ∃ F : Fam n, ParamS ε F ∧ ExhaustS ε F

end GlobalTheory.Published
