import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsFrame

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section DualIndex

variable {E : Type} [Field E] [NumberField E] [StarRing E]

abbrev qModule (S : HSpace E) : Module ℚ S.V := Module.compHom S.V (algebraMap ℚ E)

theorem qsmul_def (S : HSpace E) (q : ℚ) (v : S.V) :
    letI := qModule S; q • v = (algebraMap ℚ E q) • v := rfl

end DualIndex

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
