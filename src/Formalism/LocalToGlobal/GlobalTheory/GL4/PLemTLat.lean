import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTEmb
import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTArith
import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover

noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Basis

def GQ (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) : Matrix ι ι ℚ :=
  fun i j ↦ Algebra.trace ℚ E (S.hT (e i : S.V) (e j : S.V))

def GR (S : HSpace E) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] (e : Basis ι ℤ L) : Matrix ι ι ℝ :=
  (GQ S L e).map (Rat.castHom ℝ)

end Basis

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
