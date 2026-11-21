import Mathlib
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.CoefCol
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Formalism.LocalToGlobal.Columns.RowFormsNZp

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Pt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} [NeZero n]
  {SG : Finset (HeightOneSpectrum (𝓞 E))}

def nzPt (a : GLG E n SG) : DecoSet E n ∅ SG := ((1 : UF E n), a) • DecoSet.base E n ∅ SG

theorem nzPt_be (a : GLG E n SG) (w : SG) (x : Sp E n) :
    (nzPt a).1.be w x = (a w).1.mulVec ((Deco.base E n ∅ SG).be w x) := rfl

end Pt

section Comb

variable {n : ℕ}

variable (κ : Type) [CommRing κ]

def nzN (n r : ℕ) (i0 : Fin n) : Matrix (Fin n) (Fin n) κ := Matrix.of fun a b => if r ≤ a.val ∧ b = i0 then 1 else 0

theorem nzN_apply {r : ℕ} (i0 a b : Fin n) : nzN κ n r i0 a b = if r ≤ a.val ∧ b = i0 then 1 else 0 := rfl

variable {κ}

end Comb

end Formalism.L2.Col
