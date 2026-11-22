import Formalism.HermitianCurvature.StatementTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutoffIteratedFDerivBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.Topx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def chi0 (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem base_cutoff_is_truncation : C6.IsCut0 chi0 := by
  unfold C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp (f := fun x : ℝ => 2 * x - 1) (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

end helpers

end Formalism.FourierDecayAlt.P.Topx2
