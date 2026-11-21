import Mathlib
import GroundTheory.AutomorphicForms.HermitianValues

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Global

section LocCongr

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def LocCongr (K : Type*) [Field K] [Algebra K E] [Algebra.IsQuadraticExtension K E] (R : Type*)
    [CommRing R] [Algebra K R] (H H' : Matrix ι ι E) : Prop :=
  IsCongr (conjBase K E R) (H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E))
    (H'.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E))

variable {R : Type*} [CommRing R] [Algebra K R]

theorem LocCongr.symm {H H' : Matrix ι ι E} (h : LocCongr K R H H') : LocCongr K R H' H :=
  IsCongr.symm h

variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

end LocCongr

end GroundTheory.Automorphic
