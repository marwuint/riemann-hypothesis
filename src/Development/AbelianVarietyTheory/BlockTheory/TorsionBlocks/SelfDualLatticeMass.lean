import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass

open NumberField Formalism.BasicNotions

section Std

variable (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)

open Formalism.MainNotions.StandardLattice

omit [NumberField E] in
theorem stdForm_apply (x y : Fin M → E) : stdForm E M x y = ∑ i, star (x i) * y i := rfl

end Std

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass
