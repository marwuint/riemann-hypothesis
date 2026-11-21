import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChartSiegelNormalizedBlowup

namespace GlobalTheory.SiegJoin

theorem chartSt5_holds : ChartSt5 :=
  fun g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j _ BD hM hB =>
    ⟨_root_.GlobalTheory.BlowSmooth.smoothOfRelativeDimension_blowup g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB,
      _root_.GlobalTheory.AllChart.preChart_all g hg φ h₁ h₂ n hn ho F Z z i OZ d S π j BD hM hB⟩

end GlobalTheory.SiegJoin
