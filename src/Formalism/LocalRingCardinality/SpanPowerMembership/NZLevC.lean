import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevB
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
import Formalism.LocalToGlobal.GroupLattices.FockModels.SpanTopOf
import Formalism.SharpRestriction.GrowthBounds.DataG

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

abbrev nuV (v : Fin P.nV) (s : Fin (P.n' v)) : Fin (P.m + 1) → ℕ := nuOf (lamAt (P.lam0 v) s)

abbrev IdxV (v : Fin P.nV) (s : Fin (P.n' v)) : Type := ↥(ssIdx (P.m + 1) (P.m + 1) (nuV P v s))

instance (v : Fin P.nV) (s : Fin (P.n' v)) : Finite (IdxV P v s) := (sSIdxFinite _ _ _).to_subtype

def prodF (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) : P.Xsp :=
  ∏ v, P.vEmb v (∏ s, blockEmb Kf s (F v s))

def EV : P.Xsp := prodF P fun v s => hw Kf le_rfl (nuV P v s)

end Formalism.BasicNotions.Examples₂.NZ
