import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.GLP

open Representation

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

def cS (T : GoodSet K G) (s : T.S) (x : G) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)

end PI.Dv.GLP
