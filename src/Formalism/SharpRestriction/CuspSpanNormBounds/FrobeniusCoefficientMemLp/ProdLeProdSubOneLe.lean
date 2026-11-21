import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds

section Perm

variable {d : ℕ} (c : Composition d)

def bsig (i : Fin d) : Fin d :=
  ⟨c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i, by
    have a1 := c.sizeUpTo_index_le i
    have a2 := c.lt_sizeUpTo_index_succ i
    simp only [Fin.val_succ] at a2
    have a3 : c.sizeUpTo ((c.index i : ℕ) + 1) ≤ d := c.sizeUpTo_le _
    omega⟩

theorem bsig_val (i : Fin d) :
    ((bsig c i : Fin d) : ℕ) = c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i := rfl

end Perm

end Formalism.MainNotions.S.Pv.HH

end
