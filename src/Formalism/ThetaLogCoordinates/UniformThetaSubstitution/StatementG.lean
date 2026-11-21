import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.GaussJetBounds.StatementP

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

section Shape

variable {ν : ℕ}

def alG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  if s ∈ TT then (univ.filter (fun c => hts s c = 1)).card else 0

def capG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  colN s - alG TT colN hts s

def lsG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  ∑ c, hts s c - alG TT colN hts s

end Shape

end Formalism.InvariantFactorPaths.G7
