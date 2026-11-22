import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevL
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColA

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField Formalism.MainNotions.Inhab

section One

variable {R : Ranks} {H : Host R} {p : ℕ}

end One

variable (D : D7) (h1 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0))
  (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

end Formalism.BasicNotions.Examples₂.NZ
