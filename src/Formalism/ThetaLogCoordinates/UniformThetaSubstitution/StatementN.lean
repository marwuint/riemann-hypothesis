import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

structure PlaceData (K : Type) (r0 r1 : ℕ) where

  ν : ℕ

  hν : NeZero ν

  u : ZMod (2 * ν) → K

  TT : Finset (ZMod (2 * ν))

  ξ : ZMod (2 * ν) → Fin r0 → K

  e : TpV ν r1 → ℕ

  C : ℕ

  l : Fin C → ℕ

  sf : Fin C → ZMod (2 * ν)

  T : ∀ c, Fin (l c) → Fin r0 → K

  I : ∀ c, Fin (l c) → Fin r1

  J : Finset (Fin r1)

  kind : Fin 3

attribute [instance] PlaceData.hν

namespace PlaceData

end PlaceData

end Formalism.InvariantFactorPaths.G7
