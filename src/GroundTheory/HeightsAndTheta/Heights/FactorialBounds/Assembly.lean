import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PTorsionEquidistribution
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSupOfOrthonormalSum
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSlopeParameterChoice

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

theorem TorsionEquidistribution.full : TorsionEquidistribution.Statement :=
  TorsionEquidistribution.proof

theorem SupOfOrthonormalSum.full : SupOfOrthonormalSum.Statement.{u, v} :=
  SupOfOrthonormalSum.proof

theorem SlopeParameterChoice.full : SlopeParameterChoice.Statement :=
  SlopeParameterChoice.proof

end GroundTheory.Heights₂.Heights
