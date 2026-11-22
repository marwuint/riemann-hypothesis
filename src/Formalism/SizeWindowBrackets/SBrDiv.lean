import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
import Formalism.LogFactorialIndices.StatementSize
import Formalism.HarderNarasimhan.QuotRealize

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

section Defs4
variable {K : Type} [Field K] [NumberField K]

def lw (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)

def lcv [StarRing K] {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (L : Submodule (𝓞 K) (Fin d → K)) : ℝ :=
  (2 / (finrank ℚ K : ℝ)) * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X L)

def plOf (w : HeightOneSpectrum (𝓞 K)) : slopeLatticeData.FinPl K := ⟨w.asIdeal, w.isMaximal⟩

end Defs4

end Formalism.LFunctionChainParameters.LBrDiv
