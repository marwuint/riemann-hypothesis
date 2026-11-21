import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  (K' : Type) [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']

abbrev ext (A : HLat K) (N : Submodule (𝓞 K) A.V) : Submodule (𝓞 K') (baseChange K' A).V :=
  (baseChange K' (withL A N)).L

end

end Formalism.L2.Geo.ExtensionFiltration.ExtInvSk
