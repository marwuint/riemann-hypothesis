import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevD
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

theorem gPos_diag (v : Fin P.nV) (s : Fin (P.n' v)) (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) (a : Fin (P.m + 1)) :
    P.gPos v s A a a = P.ι v ((P.σ v ^ s.val) (A a a)) := rfl

end Formalism.BasicNotions.Examples₂.NZ
