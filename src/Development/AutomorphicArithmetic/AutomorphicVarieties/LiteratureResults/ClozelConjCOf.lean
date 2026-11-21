import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

noncomputable section

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

namespace UpperTheory.V.Lit

def FinExC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∃ τ, IsFinComp π τ

end UpperTheory.V.Lit
