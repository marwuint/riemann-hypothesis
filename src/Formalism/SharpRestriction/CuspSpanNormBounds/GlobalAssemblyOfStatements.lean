import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusGlobal

export Formalism.MainNotions.S.UnitaryVolumeMass (DefiniteComplementRank Lem1 Lem2 LatticeSpanEquality ThmA HyperplaneEquality ThmB)

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def adm1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stGlue D

end Formalism.MainNotions.VanishingOnXAndXPlusGlobal

end
