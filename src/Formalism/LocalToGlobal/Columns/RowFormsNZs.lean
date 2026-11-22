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

end Pt

section Comb

variable {n : ℕ}

variable (κ : Type) [CommRing κ]

variable {κ}

end Comb

end Formalism.L2.Col
