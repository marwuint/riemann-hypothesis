import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevD
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices
import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

end Formalism.BasicNotions.Examples₂.NZ
