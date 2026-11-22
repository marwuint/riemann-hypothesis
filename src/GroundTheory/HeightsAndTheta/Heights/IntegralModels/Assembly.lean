import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueFrame
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Imports
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
