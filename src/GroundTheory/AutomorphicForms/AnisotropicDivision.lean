import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicRestrict
import GroundTheory.AutomorphicForms.AnisotropicHeight
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]

section General

variable {A : Type*} [Ring A] [Algebra K A] (b : Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

variable {R}

variable (R)

def normCoords (y : κ → R) : Fin 1 → R := fun _ => (rmat b R ((coords b R).symm y)).det

variable {R}

end General

section Division

variable [NumberField K] {D : Type*} [DivisionRing D] [Algebra K D] {d : ℕ} (b : Basis (Fin d) K D)

def rmatUnits (R : Type*) [CommRing R] [Algebra K R] : (R ⊗[K] D)ˣ →* GL (Fin d) R :=
  Units.map (rmatHom b R : R ⊗[K] D →ₐ[R] Matrix (Fin d) (Fin d) R).toRingHom.toMonoidHom

theorem rmatUnits_val (R : Type*) [CommRing R] [Algebra K R] (x : (R ⊗[K] D)ˣ) :
    (rmatUnits b R x : Matrix (Fin d) (Fin d) R) = rmat b R x := rfl

def normOneUnits : Subgroup (𝔸[K] ⊗[K] D)ˣ :=
  (Reduction.normOneGL K d).comap (rmatUnits b 𝔸[K])

theorem mem_normOneUnits {x : (𝔸[K] ⊗[K] D)ˣ} :
    x ∈ normOneUnits b ↔ rmatUnits b 𝔸[K] x ∈ Reduction.normOneGL K d := Iff.rfl

end Division

end Anisotropic

end

end GroundTheory.Automorphic
