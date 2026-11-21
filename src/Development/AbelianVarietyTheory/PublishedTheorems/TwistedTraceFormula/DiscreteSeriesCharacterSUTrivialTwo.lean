import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep repVia CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open GlobalTheory.DSSU (SUJ SUset IsParS IsHCS)
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.SUChar

variable {n : ℕ}

def suMat (ε : Fin n → Bool) : SUJ ε →* Matrix (Fin n) (Fin n) ℂ := (ujMat ε).comp (SUJ ε).subtype

def suTorusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) : SUJ ε :=
  ⟨torusPt ε θ, by
    change (ujMat ε (torusPt ε θ)).det = 1
    rw [ujMat_torusPt, det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, hθ]
    simp⟩

theorem suMat_suTorusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) :
    suMat ε (suTorusPt ε θ hθ) = diagonal fun a => Complex.exp (θ a * Complex.I) := rfl

end GlobalTheory.SUChar

namespace GlobalTheory.Published

end GlobalTheory.Published

end
