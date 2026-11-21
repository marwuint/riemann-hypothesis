import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqMain
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Norm

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

instance (PP : Pl D.host.E) : Finite (kP PP)ˣ := Finite.of_injective _ Units.val_injective

end Norm

end Formalism.IndefR.Eqv.Act

end
