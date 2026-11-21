import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexCalculation.IsLocalizedModuleToSpan

noncomputable section

namespace PI.Dv.IdxW

open NumberField IsDedekindDomain Module

variable {K : Type} [Field K] [NumberField K]

instance instIsPrimeW (w : HeightOneSpectrum (𝓞 K)) : w.asIdeal.IsPrime := w.isPrime

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem lenAt_eq (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) :
    lenAt w M N = lenS w.asIdeal.primeCompl M N := rfl

end PI.Dv.IdxW
