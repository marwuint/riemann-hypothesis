import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLq
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLt
import Formalism.SharpRestriction.ElevenLe

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

theorem finrank_F_eq (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  exact D.host.der.finrank_F

theorem splitsF_g (D : D7) (i : Fin 2) : StandardLattice.SplitsF D (D.host.g i) := by
  have h := splits_sub D.host.F (D.host.g i) D.host.E (D.host.g_prime i) (D.nd.g_split i)
  rw [finrank_F_eq] at h
  exact h

theorem idxColTie_holds (D : D7) : IdxColTie D := idxColTie_of D (splitsF_g D)

theorem idxRowTie_holds (D : D7) : IdxRowTie D := idxRowTie_of D (splitsF_g D)

end Formalism.MainNotions.J

end
