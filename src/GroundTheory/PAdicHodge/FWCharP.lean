import Mathlib
import GroundTheory.PAdicHodge.FWGlue
import GroundTheory.PAdicHodge.TiltEquiv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Congr

variable {F F' : Type*} [Field F] [Field F']

def conjAlgEquiv {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M] (e : F ≃+* F')
    (E : L ≃+* M) (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c)) (σ : L ≃ₐ[F] L) :
    M ≃ₐ[F'] M :=
  AlgEquiv.ofRingEquiv (f := E.symm.trans (σ.toRingEquiv.trans E)) fun c => by
    have h1 : E.symm (algebraMap F' M c) = algebraMap F L (e.symm c) := by
      rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
    rw [h1, AlgEquiv.commutes, hE, RingEquiv.apply_symm_apply]

theorem conjAlgEquiv_apply {L M : Type*} [Field L] [Field M] [Algebra F L] [Algebra F' M]
    (e : F ≃+* F') (E : L ≃+* M) (hE : ∀ c, E (algebraMap F L c) = algebraMap F' M (e c))
    (σ : L ≃ₐ[F] L) (x : M) : conjAlgEquiv e E hE σ x = E (σ (E.symm x)) :=
  rfl

end Congr

end GroundTheory.PAdicHodge
