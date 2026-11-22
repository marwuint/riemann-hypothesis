import Mathlib
import GroundTheory.PAdicHodge.SlopeRobbaDegree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Module Matrix

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

namespace FrobeniusLift

variable (F : FrobeniusLift K)

end FrobeniusLift

namespace PhiModule

variable {R : Type*} [CommRing R] {φ : R →+* R}

theorem IsStable.smul {M : Type*} [AddCommGroup M] [Module R M] {ψ : R →+* R} {Ψ : M →ₛₗ[ψ] M}
    {N : Submodule R M} (h : IsStable Ψ N) (c : R) : IsStable (c • Ψ) N :=
  fun x hx => N.smul_mem c (h x hx)

end PhiModule

namespace PhiModule

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M]
variable (F : FrobeniusLift K)

def twistUnit (c : ℤ) : (Robba K)ˣ :=
  (Robba.isUnit_single 0 (zpow_ne_zero (-c) (dvUnif_ne_zero (K := K)))).unit

variable [Module.Free (Robba K) M] [Module.Finite (Robba K) M] {F}

def degSub (v : UnitOrd (Robba K) F.phi) (Φ : M →ₛₗ[F.phi] M) (N : Submodule (Robba K) M)
    (h : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] : ℤ :=
  letI := free_of_saturated N
  letI := finite_of_saturated N
  deg v (restrict Φ N h)

end PhiModule

namespace PhiModule

variable {F : FrobeniusLift K}
variable {A B : Type*} [AddCommGroup A] [Module (Robba K) A] [Module.Free (Robba K) A]
  [Module.Finite (Robba K) A] [AddCommGroup B] [Module (Robba K) B] [Module.Free (Robba K) B]
  [Module.Finite (Robba K) B]

section Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

end Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

end PhiModule

end GroundTheory.PAdicHodge
