import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.GLP

open Representation

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

def cS (T : GoodSet K G) (s : T.S) (x : G) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s x⁻¹)

theorem eS_eq (T : GoodSet K G) (s : T.S) :
    eS T s = ∑ x : G, cS T s x • MonoidAlgebra.of K G x := rfl

end PI.Dv.GLP
