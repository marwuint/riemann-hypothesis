import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColSlopeEq
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree

theorem translate_span_eq : TSpanEqVV := by
  intro K _ _ ι _ n lam
  unfold TSpan VV Formalism.GradedWeylDivisibility.tensorLat
  simp only [nablaSq_eq_delSq]
  rfl

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
