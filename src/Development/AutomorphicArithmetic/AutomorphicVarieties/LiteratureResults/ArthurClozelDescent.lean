import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.V.Lit

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

omit [IsTotallyReal E] in

def IsAdExt (σ : E →+* E) (s : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 E) E) : Prop :=
  Continuous s ∧ ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (σ x)

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

variable [Algebra F E]

end Defs

end UpperTheory.V.Lit
