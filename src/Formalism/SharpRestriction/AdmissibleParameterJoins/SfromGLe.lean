import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLb
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxColTie (D : D7) : Prop := StandardLattice.idxPi D (D.host.g 0) (D.host.g 1) = S.gaG D

def IdxRowTie (D : D7) : Prop := StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) = LocalBesselAndTopKernel.idxRows D

end Formalism.MainNotions.J

end
