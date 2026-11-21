import Mathlib
import Formalism.GaussValuationBounds.Statement

noncomputable section

namespace Formalism.NOK

open scoped ENNReal

def gaussV {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ)
    (f : PowerSeries O) : ℝ≥0∞ :=
  ⨅ n : ℕ, (((IsDiscreteValuationRing.addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) +
    ENNReal.ofReal (x * n)

def GaussMul : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 < x →
    ∀ f g : PowerSeries O, gaussV x (f * g) = gaussV x f + gaussV x g

def GaussAdd : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ),
    ∀ f g : PowerSeries O, min (gaussV x f) (gaussV x g) ≤ gaussV x (f + g)

def GaussC : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 ≤ x →
    ∀ c : O, gaussV x (PowerSeries.C c) =
      ((IsDiscreteValuationRing.addVal O c : ℕ∞) : ℝ≥0∞)

def GaussUnit : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 ≤ x →
    ∀ u : PowerSeries O, IsUnit u → gaussV x u = 0

end Formalism.NOK
