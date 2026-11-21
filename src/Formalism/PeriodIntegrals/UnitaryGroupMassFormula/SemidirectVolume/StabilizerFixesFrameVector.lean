import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem stabilizer_fixes_frame_vector {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P) (a : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [S0, mem_stabT] at hg
  have := hg (Fin.castSucc a)
  simpa [F0, Fin.snoc_castSucc] using this

end Gen

end PI.VolSemiDirect.W
