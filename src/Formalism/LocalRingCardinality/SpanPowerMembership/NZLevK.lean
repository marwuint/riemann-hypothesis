import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevH
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLPa
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataLPb
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf) (hp : (p : Kf) ≠ 0) (C : Type) [Fintype C] [DecidableEq C]

abbrev gatC : GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := C
  lev := fun _ => levB P hp
  e := 0

variable (v0 : Fin P.nV)

end Formalism.BasicNotions.Examples₂.NZ
