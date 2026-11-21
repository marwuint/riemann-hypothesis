import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TraceConjTransposeMulSelf
import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice

open Matrix Module NumberField
open scoped ComplexOrder

namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

noncomputable section

namespace Model

def c0 : Fin 20 → ℂ := fun _ => 2 * Complex.I
def r0 : Fin 20 → ℕ := fun u => if u = 0 then 1 else 2
end Model

namespace Model

section Lat

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

def bW : Basis (Fin 1) K K := Basis.singleton (Fin 1) K
def bV (i : Fin 20) : Basis (Fin (r0 i)) K (Fin (r0 i) → K) := Pi.basisFun K (Fin (r0 i))
def LN (i : Fin 20) : Submodule (𝓞 K) (Fin (r0 i) → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin (r0 i))))
def MB (i : Fin 20) : Matrix (Fin 1) (Fin (r0 i)) K := fun _ j => if j.val = 1 then -2 else 0
def BB (i : Fin 20) : (Fin (r0 i) → K) →ₗ[K] K := Matrix.toLin (bV K i) (bW K) (MB K i)

end Lat

end Model

end

end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
