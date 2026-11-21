import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsDualFlag {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) :
    Prop where
  iso : IsIsoSub B f
  pair : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram * f = 1
  perpA : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * f = 0
  perpZ : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) f * B.gram).mulVec d.z = 0

end Formalism.L2.Theta

end
