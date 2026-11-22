import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.KerRat

namespace GlobalTheory.PerQ.Model

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)

end GlobalTheory.PerQ.Model

end
