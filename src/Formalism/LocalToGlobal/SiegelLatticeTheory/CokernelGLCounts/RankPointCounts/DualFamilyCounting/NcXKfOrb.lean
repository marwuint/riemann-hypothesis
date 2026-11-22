import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousHAIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.KapIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RPGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibOfTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DetAdmA

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.KfOrbPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain
  MeasureTheory Topology Filter
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [FiniteDimensional F E]

theorem projV_eq_map (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :
    projV v X = X.map (tensMap (E := E) (evalV F v)) := rfl

end SlopeTestRemainingChoices

end Formalism.L2.SG.Pf.NcX.KfOrbPf
