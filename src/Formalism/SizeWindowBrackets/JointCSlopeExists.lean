import Mathlib
import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic

open Module NumberField
open scoped Pointwise

noncomputable section

namespace Formalism.LFunctionChainParameters.LJC

open Formalism.HN Formalism.LFunctionChainParameters.slopeLatticeData

section Str

variable {K : Type} [Field K] [NumberField K]

def rlocToK (w : FinPl K) : Rloc w →+* K :=
  haveI := w.2.isPrime
  IsLocalization.lift (M := w.1.primeCompl) (S := Rloc w) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ fun h0 => y.2 ?_
    have : (y : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0)
    rw [this]; exact Ideal.zero_mem _)

@[reducible] def rlocAlgebra (w : FinPl K) : Algebra (Rloc w) K := (rlocToK w).toAlgebra

@[reducible] def rlocModule (w : FinPl K) (V : Type) [AddCommGroup V] [Module K V] : Module (Rloc w) V :=
  Module.compHom V (rlocToK w)

end Str

end Formalism.LFunctionChainParameters.LJC
