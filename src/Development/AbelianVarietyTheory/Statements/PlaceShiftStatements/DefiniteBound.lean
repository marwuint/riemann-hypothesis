import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

noncomputable section

namespace GlobalTheory.UCls

open NumberField Matrix GlobalTheory.AdLat ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SelfDualLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin r → E)) = ⊤ ∧
    ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ↔ x ∈ Λ

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)

def TorusBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → 1 ≤ M → Unr E → SelfDualLat G Λ →
    torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M ≤ (classNumber E * M ^ (2 * fdeg E) : ℕ)

end GlobalTheory.UCls
