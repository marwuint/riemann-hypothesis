import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWLimOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.GaugeExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PhiDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvT
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation

noncomputable section

namespace GlobalTheory.RankOneChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI

theorem rhsWLim_of_leaves (hD : HaarDens) (hQ : HypQ) (hC : HypChart) (hK : GaugeK) (hV : GaugeVolUk)
    (hT : TubeLimK) (hR : OrbRepY) : Formalism.L2.SG.Pf.WB.RhsWLim := by
  have hL : PI.RhsWLim.RhsWLim :=
    rhsWLim_of mBaseMem tBallMeas (gaugeExists_of_dens hD) (rhsHaar_of (rhsWInv_of_hypQ hQ)) haarUniq
      (constVal_of_orbit (orbitPush_of hV hK hT (hypInv_of lebInvB (coneForm_of hypTh coneVol)) hR
        (hypLocal_of chartJac hC hermitianDefectAdd) opEMeas hypLF))
  exact fun k r z z' μW μW' a a' μsec hW => hL k r z z' μW μW' a a' μsec
    ⟨hW.k_pos, hW.z_mem, hW.z'_mem, hW.T_pos, hW.T'_pos, hW.haarW, hW.haarW', hW.a_pos, hW.a'_pos, hW.massW,
      hW.massW', hW.sec⟩

theorem rhsWLim : Formalism.L2.SG.Pf.WB.RhsWLim :=
  rhsWLim_of_leaves _root_.GlobalTheory.HaarDensChart.haarDens _root_.GlobalTheory.HyperboloidPolar.hypQ _root_.GlobalTheory.HypChartPf.hypChart _root_.GlobalTheory.GaugeKExists.gaugeK _root_.GlobalTheory.GaugeVolFixer.gaugeVolUk _root_.GlobalTheory.StabTube.tubeLimK _root_.GlobalTheory.HypOrbitUnique.orbRepY

instance : Fact (Formalism.L2.SG.Pf.WB.RhsWLim) := ⟨rhsWLim⟩

end GlobalTheory.RankOneChart
