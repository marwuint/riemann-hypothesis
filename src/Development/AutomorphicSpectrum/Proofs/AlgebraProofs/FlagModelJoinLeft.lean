import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSub
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
    (GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof)
    (GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft.proof _root_.GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main
      GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorLeft.proof
      GroundTheory.Heights₂.Heights.NumbersDVR.BirationalJoin.proof)

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft
