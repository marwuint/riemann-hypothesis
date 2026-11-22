import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSFlagindep

namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement :=
  PositivityTheory.Xgn.A_s_flagindep.of_items GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
    _root_.GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main _root_.GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
