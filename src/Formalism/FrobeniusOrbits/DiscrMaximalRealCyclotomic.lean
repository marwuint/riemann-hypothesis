import Formalism.FrobeniusOrbits.Statement

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def DiscrMaximalRealCyclotomic : Prop :=
  ∀ (e : ℕ) (L : Type) [Field L] [NumberField L] (ζ : L), IsPrimitiveRoot ζ (2 ^ (e + 2)) →
    discr (F1 ζ) = 2 ^ (2 ^ e * (e + 1) - 1)

def HostDiscr : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    discr (hostE ζ a b) = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) ∧
    discr (hostF ζ a b) = 2 ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e) ∧
    discr (hostE ζ a b) = discr (hostF ζ a b) ^ 2 ∧
    (|(discr (hostE ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 2) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d)) ∧
    (|(discr (hostF ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 1) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d))

def chC (e : ℕ) : GG e →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (chD e)

end Formalism.FrobeniusOrbits
