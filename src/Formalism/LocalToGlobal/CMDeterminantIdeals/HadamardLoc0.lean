import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
import Formalism.LocalToGlobal.CMDeterminantIdeals.CoeffMemOfLoc

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder

def HadamardLoc0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K)
    (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ),
    abelian₂.I ≠ 0 → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 0 < La → (∀ σ, (H σ).PosDef) →
    (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧
      p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) →
    (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) →
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg

end Formalism.L2.LamCM
