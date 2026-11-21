import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PrimeZeta2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Summable (fun p : HeightOneSpectrum (𝓞 K) => 1 / ((p.asIdeal.absNorm : ℝ) ^ 2))

end PI.UnitaryGroupMassFormula.CntFormula
