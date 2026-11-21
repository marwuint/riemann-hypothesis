import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv

open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.ProjectiveLineModels

open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates

def stdLat (K n : Type) [Field K] [NumberField K] [Fintype n] : Submodule (𝓞 K) (n → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K n))

def inclMat (κ κ₁ : Type) [DecidableEq κ] [DecidableEq κ₁] : Matrix (κ ⊕ κ₁) κ ℂ :=
  Matrix.of fun a k => if a = Sum.inl k then 1 else 0

end Formalism.LFunctionChainParameters.ProjectiveLineModels
