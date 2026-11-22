import Formalism.SizeWindowBrackets.SBrDiv
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

lemma ph_eq (y : ℝ) : Formalism.LatticeIndexTer.ph y = ph y := rfl

end Formalism.LFunctionChainParameters.LBrDiv
