import Mathlib

noncomputable section

namespace Formalism.LatticeIndexTer

open scoped ComplexConjugate

def LogProductFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (x : L), x ≠ 0 →
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ =
      ∑ᶠ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        (FractionalIdeal.count L 𝔭
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) x) : ℝ) *
          Real.log (Ideal.absNorm 𝔭.asIdeal : ℝ)

end Formalism.LatticeIndexTer
