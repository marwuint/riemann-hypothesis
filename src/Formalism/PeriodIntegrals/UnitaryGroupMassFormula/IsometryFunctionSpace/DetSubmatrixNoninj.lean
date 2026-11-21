import Mathlib

open Matrix Finset Equiv

namespace PI.IsoFunVW

theorem finite_oe (m n : ℕ) : Finite (Fin m ↪o Fin n) :=
  Finite.of_injective (fun e : Fin m ↪o Fin n => (e : Fin m → Fin n))
    (fun _ _ h => RelEmbedding.ext (congrFun h))

end PI.IsoFunVW
