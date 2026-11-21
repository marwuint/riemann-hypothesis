import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ContinuousCoB
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction Formalism.IndefR.Fin.U1
  MeasureTheory IsDedekindDomain NumberField Topology

namespace Formalism.IndefR.Fin.DL

set_option synthInstance.maxHeartbeats 80000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cUD (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (cA D).toMonoidHom

@[simp] theorem cUD_val (x : (AE D)ˣ) : ((cUD D x : (AE D)ˣ) : AE D) = cA D (x : AE D) := rfl

def hq (D : D7) : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / cUD D

theorem hq_apply (x : (AE D)ˣ) : hq D x = x / cUD D x := rfl

end Formalism.IndefR.Fin.DL

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end
