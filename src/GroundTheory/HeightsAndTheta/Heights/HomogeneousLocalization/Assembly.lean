import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Assembly
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSCoord
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSIndex
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSContinuousFrame
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSNormConj
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSFullSupport
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSConjInvariant
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.IntegralMonoInnerEqZero

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MeasureTheory NumberField
  GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

theorem FSCoord.full : FSCoord.Statement.{u} := FSCoord.proof

theorem FSIndex.full : FSIndex.Statement.{u} := FSIndex.proof FSCoord.full

theorem FSContinuousFrame.full : FSContinuousFrame.Statement.{u} :=
  FSContinuousFrame.proof FSIndex.full ComplexMetric.RegularContinuous.full

theorem FSNormConj.full : FSNormConj.Statement.{u} := FSNormConj.proof FSIndex.full

theorem FSFullSupport.full : FSFullSupport.Statement := FSFullSupport.proof

theorem FSConjInvariant.full : FSConjInvariant.Statement := FSConjInvariant.proof

end SectionsLatticeFS

namespace ProjScheme

open SectionsLatticeFS

end ProjScheme

end

end GroundTheory.Heights₂.Heights
