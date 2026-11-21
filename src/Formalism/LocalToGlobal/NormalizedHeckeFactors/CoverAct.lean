import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End

namespace Formalism.L2.NCov

end Formalism.L2.NCov

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def SplitEx (D : D7) : Prop :=
  ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ

end Formalism.L2
