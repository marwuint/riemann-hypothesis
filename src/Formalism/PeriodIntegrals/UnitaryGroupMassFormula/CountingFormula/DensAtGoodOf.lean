import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_eq_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm

end PI.UnitaryGroupMassFormula.CntFormula
