import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.IntertwiningDense
variable {n : ℕ} {ε : Fin n → Bool}

section Integral

variable (D : Datum ε) (ν : Measure (UJ ε))

variable {D ν}

theorem IsIntegral.add {f h f' h' : UJ ε → D.V} (a : D.IsIntegral ν f h) (b : D.IsIntegral ν f' h') :
    D.IsIntegral ν (f + f') (h + h') := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  obtain ⟨i2, e2⟩ := b x v hv
  refine ⟨by simp only [Pi.add_apply, inner_add_right]; exact i1.add i2, ?_⟩
  simp only [Pi.add_apply, inner_add_right, e1, e2]
  exact (integral_add i1 i2).symm

theorem IsIntegral.smul {f h : UJ ε → D.V} (a : D.IsIntegral ν f h) (c : ℂ) :
    D.IsIntegral ν (c • f) (c • h) := fun x v hv => by
  obtain ⟨i1, e1⟩ := a x v hv
  refine ⟨by simpa only [Pi.smul_apply, inner_smul_right] using i1.const_mul c, ?_⟩
  simp only [Pi.smul_apply, inner_smul_right, e1]
  exact (integral_const_mul c _).symm

end Integral

end GlobalTheory.IntertwiningDense

end
