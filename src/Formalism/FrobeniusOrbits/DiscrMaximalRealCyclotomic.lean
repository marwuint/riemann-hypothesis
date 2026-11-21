import Formalism.FrobeniusOrbits.Statement

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def HostOrdersFrob : Prop :=
  ∀ e : ℕ, ∀ g : GG e,
    orderOf g.2 ∣ orderOf g ∧ orderOf g ∣ 2 * orderOf g.2 ∧
    ∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ), ((u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) →
      g.2 = hcl e u → orderOf g ≤ 2 ^ j →
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1)

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
