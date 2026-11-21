import Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
import Formalism.SizeWindowBrackets.GaloisToProductIsIso

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LSmall

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

section Conj

open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

def cj {m n : Type} (M : Matrix m n ℂ) : Matrix m n ℂ := M.map (starRingEnd ℂ)

end Conj

end Formalism.LFunctionChainParameters.LSmall
