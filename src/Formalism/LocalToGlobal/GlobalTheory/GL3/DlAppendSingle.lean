import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.IntegralityIffAwayAtD

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Der

variable {D : D7} {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

local notation "Ser" => MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]

def Dl (l : List (Matrix (Fin N') (Fin N) D.host.E)) (F : Ser) : Ser :=
  l.foldr (fun y' G => der D lam y' G) F

variable {lam}

theorem isPadicIntegral_add {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x + y) :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

end Der

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
