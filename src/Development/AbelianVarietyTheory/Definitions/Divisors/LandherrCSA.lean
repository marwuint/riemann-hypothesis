import Mathlib

noncomputable section
namespace GlobalTheory.HermCSA
open NumberField
open scoped TensorProduct

def ext (C K : Type) [Ring C] [CommRing K] (s : C →+ C) : K ⊗[ℤ] C →ₗ[ℤ] K ⊗[ℤ] C :=
  LinearMap.lTensor K s.toIntLinearMap

end GlobalTheory.HermCSA
