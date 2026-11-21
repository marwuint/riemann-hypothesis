import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.FJ

section Forms

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ)

def admitted (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Set (levelForms H N X) :=
  {γ | (∀ y, y ≠ 0 → 0 < (γ : LinearMap.BilinForm ℤ X) y y) ∧ ∀ y z, (2 * N : ℤ) ∣ (γ : LinearMap.BilinForm ℤ X) y z}

variable [Module (𝓞 E) X]

end Forms

end GlobalTheory.LocM.FJ
