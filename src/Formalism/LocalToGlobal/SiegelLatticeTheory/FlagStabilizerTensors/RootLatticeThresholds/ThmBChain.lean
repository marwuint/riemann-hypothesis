import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RMeasP

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.ThmBUseR
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem theoremB_uniform_rotated (h : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform) : JointNormBoundRotatedUniform := by
  exact h

end Formalism.L2.SG.Pf.ThmBChain
