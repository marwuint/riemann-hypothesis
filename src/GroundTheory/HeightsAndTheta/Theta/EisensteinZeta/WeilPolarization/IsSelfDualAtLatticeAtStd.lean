import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistence
import GroundTheory.AutomorphicForms.HermitianOrthogonal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open Module Matrix NumberField IsDedekindDomain TensorProduct GroundTheory.Automorphic

section Objects

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

def locIntegers (v : HeightOneSpectrum (𝓞 F)) :
    Subalgebra (v.adicCompletionIntegers F) (v.adicCompletion F ⊗[F] E) :=
  integralClosure _ _

variable {F E}

variable (v : HeightOneSpectrum (𝓞 F))

end Objects

section Inhabitants

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable (v : HeightOneSpectrum (𝓞 F))

def stdLatticeAt (M : ℕ) :
    Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E) where
  carrier := {x | ∀ i, x i ∈ locIntegers F E v}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  smul_mem' c x hx i := by
    rw [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
    exact mul_mem c.2 (hx i)

theorem mem_stdLatticeAt {M : ℕ} {x : Fin M → v.adicCompletion F ⊗[F] E} :
    x ∈ stdLatticeAt v M ↔ ∀ i, x i ∈ locIntegers F E v := Iff.rfl

end Inhabitants

end GroundTheory.Heights₂.Theta
