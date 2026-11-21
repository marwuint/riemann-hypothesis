import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Top4 Formalism.L2.SG.JoinSI Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.JoinSISel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def BaseVectorImageFull (D : D7) : Prop := (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : Formalism.L2.Top3.SelDH 𝒜 sel}
  {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel} {selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK}

end Formalism.L2.SG.JoinSISel
