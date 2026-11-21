import Formalism.SharpRestriction.InertJacobiLevels.LambdaRealEqShiftedWeight
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.BasicNotions.Examples₂

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0) (sc : Scale) (eOf : ℕ → ℕ)

def baseB : D.what₂.Word → ℕ → Set (G.HH D) := fun _ p => {t | ∃ x, bsA (G.stepP D p) x = t}

def rOfB : D.what₂.Word → ℕ → ℕ := fun _ p => if (p : ℝ) < sc.p0 D.R.k then G.rG sc else 1

def recB : D7 := withGatCB D h0 (rOfB D sc) eOf (baseB D)

theorem recB_e (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((recB D h0 sc eOf).gat u w hg).e = eOf (D.what₂.places.resChar w) := rfl

end Formalism.MainNotions.Inhab

end
