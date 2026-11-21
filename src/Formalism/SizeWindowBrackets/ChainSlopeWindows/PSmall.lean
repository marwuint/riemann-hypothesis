import Formalism.SizeWindowBrackets.SSmall
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LSmall

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

section Conj

open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

lemma cj_apply {m n : Type} (M : Matrix m n ℂ) (i : m) (j : n) : cj M i j = starRingEnd ℂ (M i j) := rfl

end Conj

end Formalism.LFunctionChainParameters.LSmall
