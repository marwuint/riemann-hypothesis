import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SW

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def classWeightAlt : ℝ :=
  (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f

end SW

end Formalism.MainNotions.BridgeLemma₂

end
