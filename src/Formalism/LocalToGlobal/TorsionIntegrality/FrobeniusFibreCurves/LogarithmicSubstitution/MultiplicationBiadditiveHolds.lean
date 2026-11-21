import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementC

noncomputable section

namespace Formalism.L2.Th1.B.Mul

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')

section Quot

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}

def lam (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] :
    AddSubgroup (MvPowerSeries ι K) where
  carrier := {h | Simeq h 0}
  zero_mem' := (equivalence_rules K ι).1 0
  add_mem' := fun {a b} ha hb => by
    have e := (equivalence_rules K ι).2.2.2.1 a 0 b 0 ha hb
    rwa [add_zero] at e
  neg_mem' := fun {a} ha => by
    have e := (simeqInt K ι a 0 a 0 ha ha).2.1
    rwa [neg_zero] at e

end Quot

end Formalism.L2.Th1.B.Mul
