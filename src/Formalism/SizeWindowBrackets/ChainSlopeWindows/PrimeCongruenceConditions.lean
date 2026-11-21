import Formalism.SizeWindowBrackets.SmoothedRemainderRealIntegralFormula
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Filter Topology ArithmeticFunction DirichletCharacter

noncomputable section

namespace Formalism.LFunctionChainParameters.LBr2

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

lemma psC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (psC : AddChar (E0 × H) ℂ) g = if g.1.2 = 0 then 1 else -1 := rfl

lemma chC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chC : AddChar (E0 × H) ℂ) g = if g.1.1 = 0 then 1 else -1 := rfl

lemma chpsC_apply {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (g : E0 × H) :
    (chpsC : AddChar (E0 × H) ℂ) g = (if g.1.1 = 0 then 1 else -1) * (if g.1.2 = 0 then 1 else -1) := rfl

end Formalism.LFunctionChainParameters.LBr2
