import Mathlib
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
import Formalism.LocalToGlobal.Columns.RecLevelSym

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (Gc : ChGlob X R.m)

abbrev chr0 (X : Fields) (S : Set ℕ) : Chr X.F X.E X.K := ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)

end Fin

end Formalism.L2.Ker
