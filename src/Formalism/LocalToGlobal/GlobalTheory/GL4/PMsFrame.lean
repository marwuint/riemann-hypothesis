import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SuccessiveMinima.StatementMink
import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_dualSub (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ dualSub S L ↔ ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

end Frames

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
