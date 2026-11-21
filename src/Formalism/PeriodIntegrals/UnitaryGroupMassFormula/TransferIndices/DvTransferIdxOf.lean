import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

def VNonneg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K),
    0 ≤ vAdd w (algebraMap (𝓞 K) K x)

end PI.Dv.TIW
