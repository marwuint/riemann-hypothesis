import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.OrbitPlaces

section NuPart

variable (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau)

def nuE (a : ℕ) : ℚ := if h : a < D.R.m then (D.hc τ).e ⟨a, h⟩ else 0

def nuQ (i r : ℕ) : ℚ :=
  DV.srcPar D u τ r + nuE D τ i - (((D.R.N i : ℕ) : ℚ) + ((D.R.N (i + 1) : ℕ) : ℚ) - 1 - 2 * (r : ℚ)) / 2

end NuPart

end Formalism.MainNotions.DIV.Inh

end
