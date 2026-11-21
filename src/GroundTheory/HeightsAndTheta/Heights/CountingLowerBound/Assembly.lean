import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMinkowskiCovolumeBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PCuspWeightBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PShortVectorsOrthogonal
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PPackingCount
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCountBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTailBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanLogPlus
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCuspWeight

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

universe u

theorem PackingCount.full : PackingCount.Statement :=
  PackingCount.proof

theorem MeanCountBound.full : MeanCountBound.Statement.{u} :=
  MeanCountBound.proof

theorem TailBound.full : TailBound.Statement.{u} :=
  TailBound.proof MeanCountBound.full

theorem MeanLogPlus.full : MeanLogPlus.Statement.{u} :=
  MeanLogPlus.proof TailBound.full

theorem MeanCuspWeight.full : MeanCuspWeight.Statement :=
  MeanCuspWeight.proof

end GroundTheory.Heights₂.Heights.LowerBound
