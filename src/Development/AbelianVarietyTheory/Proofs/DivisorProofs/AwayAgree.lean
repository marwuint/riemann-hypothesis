import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.EigWhole

variable {D : D7} (O : Setup D)

abbrev Var : Type := DV.Rt D.what₂.Tau O.N ⊕ (Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))

def fam (T : Finset ℕ) (R : ℝ) : Var O → Sym D.host.E →₀ ℤ
  | .inl x => rootSym O.S.Dw (ArIn.ind T) (some R) (DV.tauEmb D x.1) x.2
  | .inr l => wholeSym (ArIn.ind T) (some R) l

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

end GlobalTheory.EigWhole

end
