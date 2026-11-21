import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

theorem lamX_one (I : AutInst) : lamX I (1, 1) = I.L := by
  refine le_antisymm (fun y hy => (I.L_dual y).2 fun z hz => ?_) (GlobalTheory.Count.Test.le_lamX_one I)
  exact ((GlobalTheory.PointLattice.lamX_selfDual I (1, 1)).2.2.2.1 y).1 hy z (GlobalTheory.Count.Test.le_lamX_one I hz)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

end GlobalTheory.GaussMean.Test
