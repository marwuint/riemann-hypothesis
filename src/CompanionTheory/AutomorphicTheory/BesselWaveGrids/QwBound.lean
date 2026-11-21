import Formalism.HermitianCurvature.StatementD

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt

theorem qC_ofReal (P : M.Par) (y : ℝ) :
    M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
  simp [M.qC, I.qpoly]

end CompanionTheory.WaveGrid
