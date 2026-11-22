import Formalism.PadicSubsetSums.CentralIdempotents.FactorOverLocalSubalgebraMonic

noncomputable section

open Polynomial MeasureTheory
open scoped TensorProduct NumberField ComplexConjugate

namespace Formalism.IrreducibleCountingLemmas.Z

def DegreeOneSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ →
    P.inertiaDeg ℤ = 1 → P.ramificationIdx (𝓞 F) = 1 →
    ((P.under (𝓞 F)).primesOver (𝓞 E)).ncard = 2

def BCCyclicVector : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (g : Module.End K V), g.charpoly.Separable → ∃ e : V, ∀ v : V, ∃ p : K[X], aeval g p e = v

end Formalism.IrreducibleCountingLemmas.Z
