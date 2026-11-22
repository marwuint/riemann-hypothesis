import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.RecLevelLocF

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.UG.P

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

variable (h : BasePi ST π)

variable (SG : Finset (Pl E)) (c₀ : DiaG E ST)

end Loc

end Formalism.L2.Col
