import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

def fT (L : PeriodPair) (t z : ℂ) : ℂ := opU L t (sgStar L) z / sgStar L z

def thetaZeroCharacter (L : PeriodPair) (ω₀ ω : ℂ) : ℂ :=
  semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))

def OpUTh0 : Prop :=
  ∀ (L : PeriodPair) (t x z : ℂ),
    opU L x (th0 L t) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x t : ℂ)) * opU L (x + t) (sgStar L) z
        / opU L t (sgStar L) 0

def ThetaZeroLine : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (F : ℂ → ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, F (z + ω) = thetaZeroCharacter L ω₀ ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * F z) →
    ∀ z, F z = F 0 * th0 L (ω₀ / 2) z

end Formalism.L2.Th1.F
