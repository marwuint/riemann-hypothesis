import Formalism.SizeWindowBrackets.SlopeHypothesesRounded
import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
import Formalism.LogVandermondeBounds.LogRatioUpperBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds

open Real

namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer

namespace Model

lemma h6 : (6 : ℝ) ≤ Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith

end Model

end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
