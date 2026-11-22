import Formalism.LocalToGlobal.Columns.TiedGlPl
import Formalism.LocalToGlobal.Columns.TiedGlMat
import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.HermitianForms.FormsTied

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section GLc

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ)

end GLc

end Formalism.L2.Col
