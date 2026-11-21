import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero

namespace DualFramesAlt.EigenUniformiser

open PowerSeries

structure Data (O : Type*) [CommRing O] (Δ : Type*) [Group Δ] [Fintype Δ] where
  ρ : Δ →* (PowerSeries O ≃ₐ[O] PowerSeries O)
  ω : Δ →* Oˣ
  hω : Function.Injective ω
  v : Δ → PowerSeries O
  hv : ∀ δ, ρ δ X = X * v δ
  hv0 : ∀ δ, constantCoeff (v δ) = (ω δ : O)

variable {O : Type*} [CommRing O] [IsDomain O] {Δ : Type*} [Group Δ] [Fintype Δ] [IsCyclic Δ]

end DualFramesAlt.EigenUniformiser
