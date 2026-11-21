import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Mod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def toO (M : Model F E) : 𝒪[F] →+* M.L.O where
  toFun x := ⟨algebraMap F E (x : F), (M.L.O_def _).2 (isIntegral_algebraMap (x := x))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma toO_coe (M : Model F E) (x : 𝒪[F]) : ((toO M x : M.L.O) : E) = algebraMap F E (x : F) := rfl

variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

end Mod

end PI.NGStepBBW
