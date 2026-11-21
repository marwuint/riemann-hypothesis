import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesPt

noncomputable section

namespace Formalism.MainNotions.S.ThB

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.S.Pv.Frames

variable (D : D7)

def JSqRot {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) : ENNReal :=
  ∏ v, orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ))

def BSumRot {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (W : Point D.host.E (D.R.rS + 1) → ℝ) : ENNReal :=
  ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ},
    ENNReal.ofReal (wPt D γ.1 * ptWeightG D (rhoReal D) T T' γ.1.1 * W γ.1) * JSqRot D X γ.1

end Formalism.MainNotions.S.ThB
