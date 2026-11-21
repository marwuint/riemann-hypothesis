import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

open Complex Filter Topology

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain6.Chi8

open Formalism.ZF.ComplexPowerDifferenceIntegral

def chi : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

lemma chi_apply (x : ZMod 8) : chi x = ((ZMod.χ₈ x : ℤ) : ℂ) := rfl

end Formalism.LFunctionChainParameters.LChain6.Chi8

namespace Formalism.LFunctionChainParameters.LChain6

end Formalism.LFunctionChainParameters.LChain6
