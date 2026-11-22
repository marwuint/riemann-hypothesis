import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix MvPolynomial NumberField Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def SelfDualP (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E))

end Formalism.L2.GlobalTheoryTheory.Br
