import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section Glue

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]

abbrev primeTo (p : Nat.Primes) : Submonoid ℤ := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl

instance (p : S) : IsLocalization (primeTo (p : Nat.Primes)) (o p) := inferInstance

variable (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E)

variable {B₀ Bp}

end Glue

end GroundTheory.Heights₂.Heights.Model
