import Mathlib
import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

open Module PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

variable {R : Type} [AddCommGroup R] [Module O R]

abbrev Aq (O : Type) [CommRing O] (k : ℕ) := PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k}

abbrev Aql (O : Type) [CommRing O] (k c : ℕ) (l : O) :=
  PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)}

theorem spanX_le (k c : ℕ) (l : O) :
    Ideal.span {(X : PowerSeries O) ^ k} ≤ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)} :=
  Ideal.span_mono (by simp)

def red (k c : ℕ) (l : O) : Aq O k →ₐ[O] Aql O k c l := Ideal.Quotient.factorₐ O (spanX_le k c l)

theorem red_mk (k c : ℕ) (l : O) (a : PowerSeries O) :
    red k c l (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount
