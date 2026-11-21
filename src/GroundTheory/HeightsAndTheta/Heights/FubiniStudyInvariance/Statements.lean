import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace CP

variable {N : ℕ}

lemma unitary_injective (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) :
    Function.Injective (Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  intro v w h
  have hU : star (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * U = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h' := congrArg (fun x => star (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) *ᵥ x) h
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hU] using h'

def unitaryAct (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) : CP N → CP N :=
  Projectivization.map (Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))
    (unitary_injective U)

lemma unitaryAct_mk (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    unitaryAct U (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) v)
        (fun h0 => hv (unitary_injective U (by rw [h0, map_zero]))) := rfl

end CP

namespace FSInv

end FSInv

end

end GroundTheory.Heights₂.Heights
