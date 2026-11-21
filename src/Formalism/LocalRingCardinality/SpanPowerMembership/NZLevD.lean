import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevC

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

instance : Infinite Kf := Infinite.of_injective (Nat.cast : ℕ → Kf) Nat.cast_injective

end Formalism.BasicNotions.Examples₂.NZ
