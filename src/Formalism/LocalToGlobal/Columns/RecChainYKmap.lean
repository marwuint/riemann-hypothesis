import Formalism.LocalToGlobal.Columns.RecChainYUnfPol
import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.Columns.GFamSEv

open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker Formalism.L2.Col

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev SecY (u : Pr.Word) (m2 : ℕ) : Type := ∀ j b, ((Formalism.L2.Col.chFY W sel mu cst L u m2 j).mem b).Sec

variable {W sel mu cst L}

variable {Ch}

end Charts

end Formalism.L2.Col.Sc
