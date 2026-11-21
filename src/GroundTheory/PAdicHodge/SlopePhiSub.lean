import Mathlib
import GroundTheory.PAdicHodge.SlopePhiModule
import GroundTheory.PAdicHodge.SlopeBezout
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace PhiModule

open Matrix Module

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {φ : R →+* R}
variable {M : Type*} [AddCommGroup M] [Module R M]

def IsStable (Φ : M →ₛₗ[φ] M) (N : Submodule R M) : Prop := ∀ x ∈ N, Φ x ∈ N

def restrict (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) : N →ₛₗ[φ] N where
  toFun x := ⟨Φ (x : M), h _ x.2⟩
  map_add' x y := Subtype.ext (map_add Φ (x : M) y)
  map_smul' r x := Subtype.ext (Φ.map_smulₛₗ r (x : M))

@[simp] theorem coe_restrict_apply (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N)
    (x : N) : (restrict Φ N h x : M) = Φ (x : M) := rfl

def quot (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) :
    (M ⧸ N) →ₛₗ[φ] (M ⧸ N) :=
  N.mapQ N Φ h

@[simp] theorem quot_mk (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) (x : M) :
    quot Φ N h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Φ x) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Bezout

variable [IsDomain R] [IsBezout R] [Module.Free R M] [Module.Finite R M]

theorem free_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] : Module.Free R N :=
  free_of_isTorsionFree_quotient N

theorem finite_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] :
    Module.Finite R N :=
  finite_of_isTorsionFree_quotient N

end Bezout

section Subquot

variable {Φ : M →ₛₗ[φ] M} {N N' : Submodule R M}

abbrev inSub (N N' : Submodule R M) : Submodule R N' := N.comap N'.subtype

end Subquot

end PhiModule

end GroundTheory.PAdicHodge
