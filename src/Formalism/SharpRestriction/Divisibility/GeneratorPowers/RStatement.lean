import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

open Classical in

def clOf {j : ℕ} (wL : WeightFamilies.Wt D j) {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  if ((D.host.QS : ℕ) : 𝓞 K) ∈ la.asIdeal then (padicValNat (ringChar (𝓞 K ⧸ la.asIdeal)) D.host.QS : ℝ) * (c2 D wL : ℝ)
  else if ((D.host.q : ℕ) : 𝓞 K) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 K) ∈ la.asIdeal then (cHalf wL : ℝ)
  else 0

end Formalism.MainNotions.ModuliIntegralCharts.H1
