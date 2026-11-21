import Formalism.LocalToGlobal.Columns.TiedUpDnA
import Formalism.LocalToGlobal.Columns.TiedVal

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance tud_kerPrime {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    (RingHom.ker (Ideal.Quotient.mk P.asIdeal)).IsPrime :=
  RingHom.ker_isPrime _

end Formalism.L2.Col
