import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib
import Formalism.PeriodIntegrals.LpLower
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace Formalism.BasicNotions

open Formalism.MainNotions.G
open scoped BigOperators

theorem tauPl_bij (D : D7) : Function.Bijective (tauPl D) := by
  have hI := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨β, t⟩ ⟨β', t'⟩ h
    have h1 : plGG D (β, t) = plGG D (β', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases β <;> cases β'
    · have h2 : D.R.tau1 t = D.R.tau1 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
    · exact absurd (show D.R.tau1 t = D.R.tau2 t' from h1) (hP.2 t t')
    · exact absurd (show D.R.tau1 t' = D.R.tau2 t from h1.symm) (hP.2 t' t)
    · have h2 : D.R.tau2 t = D.R.tau2 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨(false, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩
    · exact ⟨(true, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩

theorem factDelDualNabla : FactDelDualNabla := factDelDualNabla_of Formalism.L2.DIV.weylEqDualNabla

end Formalism.BasicNotions

end
