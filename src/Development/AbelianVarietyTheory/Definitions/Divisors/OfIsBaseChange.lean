import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.UG Formalism.BasicNotions
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.PRep

namespace GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def locR (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin N) (w.adicCompletion E)) (Sm E N) :=
  (finRep E N).comp (locGL E N w)

end GlobalTheory.ResW

end
