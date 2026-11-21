import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def conjId (D : D7) : (AE D)ˣ →* (AE D)ˣ := Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def IsHeckeCharF (D : D7) (χ : (AF D.host.F)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ a : D.host.Fˣ, χ (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1

end Formalism.L2.Theta

end
