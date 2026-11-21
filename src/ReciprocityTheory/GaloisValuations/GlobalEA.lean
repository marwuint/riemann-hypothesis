import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.Hypotheses.Descent

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section res

variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]

@[simp] theorem resGal_apply (σ : G L Ω) (x : Ω) : resGal F L Ω σ x = σ x := rfl

theorem isAlgClosure_top [IsAlgClosure F Ω] : IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) L⟩

end res

end ReciprocityTheory.Gal
