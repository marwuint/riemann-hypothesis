import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarProved
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensPf
import Mathlib
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibOfTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.KapIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RPGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DetAdmA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousHAIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXKfOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXWSp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.HformSmulLeft
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AprimeInf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstFinal

namespace Formalism.L2.SG.Closed

theorem AprimeInf_holds [hG : Fact PI.AprimeInfW.GaugeVolUD] : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  PI.AprimeInfAsm.aprime_infinite_real Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds hG.out

variable [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem JacGauge_holds : Formalism.L2.SG.Pf.JacGauge := Formalism.L2.SG.Pf.jacGauge

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] in
theorem RealBracket_holds (hC : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) : Formalism.L2.SG.Pf.NcReal.RealBracket :=
  Formalism.L2.SG.Pf.NcReal.JX.realBracket_of_jac JacGauge_holds hC AprimeInf_holds
    (fun n ε => Formalism.MainNotions.S.Gauge.gauge_density_exists n ε)

end Formalism.L2.SG.Closed
