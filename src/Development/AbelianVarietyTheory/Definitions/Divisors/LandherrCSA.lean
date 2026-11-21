import Mathlib

noncomputable section
namespace GlobalTheory.HermCSA
open NumberField
open scoped TensorProduct

def IsUInv (F C : Type) [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C] (s : C →+ C) : Prop :=
  (∀ x y, s (x * y) = s y * s x) ∧ (∀ x, s (s x) = x) ∧
    ∀ a : F, s (algebraMap F C a) = algebraMap F C (IsCMField.complexConj F a)

def ext (C K : Type) [Ring C] [CommRing K] (s : C →+ C) : K ⊗[ℤ] C →ₗ[ℤ] K ⊗[ℤ] C :=
  LinearMap.lTensor K s.toIntLinearMap

end GlobalTheory.HermCSA
