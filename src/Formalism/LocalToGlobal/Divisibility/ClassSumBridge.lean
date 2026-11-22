import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV.CSD

open Formalism.DivisionValues

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

def pairOne (K : Type) [Field K] [StarRing K] : K →ₗ⋆[K] K →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
    (by intro x y z; simp [add_mul]) (by intro a x y; simp [mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add]) (by intro a x y; simp [mul_left_comm])

end Formalism.L2.DIV.CSD
