import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.InertDeltaFirstCaseEqPower
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FBL

def LpowMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w))
  (g : UL n w → ℂ), IsOpen (K' : Set (UL n w)) → K' ≤ KL n w → IsHecke K' g → ∀ m k : ℕ, U.lpow K' (U.lpow K' g m) k = U.lpow K' g (m * k)

def EllHom : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) [MeasurableSpace (GA E a)]
  [MeasurableSpace (GA E b)] (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (c : ℂ) (φ : GA E a × GA E b → ℂ),
    ellSum2 μ₁ μ₂ (c • φ) = c * ellSum2 μ₁ μ₂ φ

def NontrivInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → Nontrivial (InfinitePlace E)

end PositivityTheory.Rg.BcB.F.FBL

end
