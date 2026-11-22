import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatio
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelOneVectorMeasurableOfCompactSupport

namespace GlobalTheory.VolRatioFromSiegelWeil

theorem volumeRatio :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D :=
  fun hP =>
    GlobalTheory.VolRatioFromSecondClause.volumeRatio
      (_root_.GlobalTheory.OneVecMeas.sw1b2_of_cc (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil hP))

end GlobalTheory.VolRatioFromSiegelWeil
