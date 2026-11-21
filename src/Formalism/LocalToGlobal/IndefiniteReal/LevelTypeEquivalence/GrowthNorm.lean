import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem infMat_eq (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) (i j : Fin V.rank) :
    infMat D.sp.cm.sig V.gram (θ τ) g i j = θ τ (infPart D (mt V g i j)) := rfl

end Formalism.IndefR.Eqv

end
