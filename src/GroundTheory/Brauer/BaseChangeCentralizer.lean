import Mathlib
import GroundTheory.Brauer.CrossedProductIso
import GroundTheory.Brauer.CrossedProductTensor
import GroundTheory.Brauer.BaseChange
import GroundTheory.Brauer.DoubleCentralizer
import GroundTheory.Brauer.Splitting
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open Module groupCohomology

open scoped TensorProduct

universe u

namespace CrossedProduct

section Restrict

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]

variable (K E) in

def resCocycle (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L ≃ₐ[E] L) × (L ≃ₐ[E] L) → Lˣ :=
  fun p => f (p.1.restrictScalars K, p.2.restrictScalars K)

@[simp]
theorem resCocycle_apply (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L ≃ₐ[E] L) × (L ≃ₐ[E] L)) :
    resCocycle K E f p = f (p.1.restrictScalars K, p.2.restrictScalars K) :=
  rfl

end Restrict

section Action

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)

variable (E) in

def inclBase : E →ₐ[K] CrossedProduct hf :=
  (incl (hf := hf)).comp (IsScalarTower.toAlgHom K E L)

end Action

end CrossedProduct

end GroundTheory.Brauer
