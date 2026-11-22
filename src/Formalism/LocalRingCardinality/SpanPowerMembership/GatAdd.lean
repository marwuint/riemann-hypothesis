import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField LevelValuationRings

def tau1P (φ : Formalism.HC.Frame) (t : φ.A) : ↥φ.Psi := ⟨φ.tau1 t, rfl⟩

theorem iotaH_nsmul (φ : Formalism.HC.Frame) (t h : φ.A) (s : ℕ) :
    φ.iota (t + s • h) = φ.iota t * φ.iota h ^ s := rfl

variable (D : D7) {p : ℕ}

variable (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0) (rOf : D.what₂.Word → ℕ → ℕ)
  (B : D.what₂.Word → ℕ → Set (HH D))

variable (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

end Formalism.BasicNotions.Examples₂
