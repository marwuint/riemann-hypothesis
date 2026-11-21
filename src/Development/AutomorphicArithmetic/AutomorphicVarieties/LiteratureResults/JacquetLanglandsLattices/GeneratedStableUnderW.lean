import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DiscreteGL2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Mathlib

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.JL

namespace UpperTheory.V.Lit.JL.DiscreteSeriesWeights

section Abstract

variable {M : Type} [AddCommGroup M] [Module ℂ M]

private structure Rel (W : Module.End ℂ M) (X : ℤˣ → Module.End ℂ M) : Prop where
  wx : ∀ (s : ℤˣ) x, W (X s x) = X s (W x) + (2 * ((s : ℤ) : ℂ) * Complex.I) • X s x
  xx : ∀ (s : ℤˣ) x, X (-s) (X s x) = X s (X (-s) x) + (4 * ((s : ℤ) : ℂ) * Complex.I) • W x

variable {V : Submodule ℂ M} {W : Module.End ℂ M} {X : ℤˣ → Module.End ℂ M} {k : ℕ}

end Abstract

section Units

variable {M : Type} [AddCommGroup M] [Module ℂ M]

private def wOp (E : Fin 2 → Fin 2 → Module.End ℂ M) : Module.End ℂ M := E 0 1 - E 1 0

private noncomputable def xOp (E : Fin 2 → Fin 2 → Module.End ℂ M) (s : ℤˣ) : Module.End ℂ M :=
  E 0 0 - E 1 1 + (((s : ℤ) : ℂ) * Complex.I) • (E 0 1 + E 1 0)

private theorem wOp_apply (E : Fin 2 → Fin 2 → Module.End ℂ M) (x : M) : wOp E x = E 0 1 x - E 1 0 x := rfl

private theorem xOp_apply (E : Fin 2 → Fin 2 → Module.End ℂ M) (s : ℤˣ) (x : M) :
    xOp E s x = E 0 0 x - E 1 1 x + (((s : ℤ) : ℂ) * Complex.I) • (E 0 1 x + E 1 0 x) := rfl

end Units

end UpperTheory.V.Lit.JL.DiscreteSeriesWeights

