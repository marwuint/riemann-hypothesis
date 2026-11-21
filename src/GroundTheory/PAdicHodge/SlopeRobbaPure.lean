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

theorem gaussNorm_phi_unit (u : (Robba K)ˣ) :
    Robba.norm1 (F.phi u) = Robba.norm1 (u : Robba K) :=
  gaussNorm_phi (Robba.unit_mem_bounded u)

theorem gaussNorm_phi_pow_unit (d : ℕ) (u : (Robba K)ˣ) :
    Robba.norm1 ((F.phi ^ d) u) = Robba.norm1 (u : Robba K) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    have hu : IsUnit ((F.phi ^ d) (u : Robba K)) := u.isUnit.map _
    have := F.gaussNorm_phi_unit hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this, ih]

def unitOrd : PhiModule.UnitOrd (Robba K) F.phi := Robba.unitOrd F.phi F.gaussNorm_phi_unit

def unitOrdPow (d : ℕ) : PhiModule.UnitOrd (Robba K) (F.phi ^ d) :=
  Robba.unitOrd (F.phi ^ d) (F.gaussNorm_phi_pow_unit d)

theorem unitOrdPow_eq (d : ℕ) : F.unitOrdPow d = F.unitOrd.pow d := rfl

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

theorem coe_twistUnit (c : ℤ) : (twistUnit (K := K) c : Robba K) = Robba.single 0 (dvUnif K ^ (-c)) := rfl

variable [Module.Free (Robba K) M] [Module.Finite (Robba K) M] {F}

def degSub (v : UnitOrd (Robba K) F.phi) (Φ : M →ₛₗ[F.phi] M) (N : Submodule (Robba K) M)
    (h : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] : ℤ :=
  letI := free_of_saturated N
  letI := finite_of_saturated N
  deg v (restrict Φ N h)

theorem degSub_eq (v : UnitOrd (Robba K) F.phi) (Φ : M →ₛₗ[F.phi] M) (N : Submodule (Robba K) M)
    (h : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.Free (Robba K) N]
    [Module.Finite (Robba K) N] : degSub v Φ N h = deg v (restrict Φ N h) := rfl

end PhiModule

namespace PhiModule

variable {F : FrobeniusLift K}
variable {A B : Type*} [AddCommGroup A] [Module (Robba K) A] [Module.Free (Robba K) A]
  [Module.Finite (Robba K) A] [AddCommGroup B] [Module (Robba K) B] [Module.Free (Robba K) B]
  [Module.Finite (Robba K) B]

section Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

def subquotMap {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z) :
    (X ⧸ inSub P X) →ₗ[Robba K] (Y ⧸ inSub Z Y) :=
  (inSub P X).mapQ (inSub Z Y) (Submodule.inclusion hXY) fun _ hx => hPZ hx

theorem subquotMap_mk {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z) (x : X) :
    subquotMap hXY hPZ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hXY x) :=
  rfl

end Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

namespace SlopeFiltration

end SlopeFiltration

end PhiModule

end GroundTheory.PAdicHodge
