import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.DivLin

section R

variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]

theorem nilPart_eq (l : ℕ) (M : I → Module.End O H) (t : I → R) :
    nilPart l M R t = (lPrime l : R) • ∑ i, t i • (M i).baseChange R := rfl

end R

end GlobalTheory.DivLin

namespace GlobalTheory.DivLin

end GlobalTheory.DivLin
