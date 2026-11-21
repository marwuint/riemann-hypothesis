import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def ETSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (R' : ℕ), 2 ≤ R' → ∀ (r : ℕ) (y z : Fin r → Y),
    (∀ a : Y, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : Y, a = u + R' • t) →
    ∀ a : Y, ∃ n : ℕ, 0 < n ∧
      n • a ∈ Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b)

end Formalism.MainNotions.ModuliIntegralCharts.H1
