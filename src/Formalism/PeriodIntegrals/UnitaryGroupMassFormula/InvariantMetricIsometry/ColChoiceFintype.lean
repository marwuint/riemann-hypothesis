import Mathlib
import Formalism.PeriodIntegrals.IsoInvMetric

noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

instance finOE (h N : ℕ) : Fintype (Fin h ↪o Fin N) :=
  haveI : Finite (Fin h ↪o Fin N) :=
    Finite.of_injective (fun e : Fin h ↪o Fin N => (e : Fin h → Fin N)) DFunLike.coe_injective
  Fintype.ofFinite _

instance colChoiceFintype {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance

end PI.IsoInvMetricW
