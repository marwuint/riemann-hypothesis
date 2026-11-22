import Formalism.SharpRestriction.InertJacobiLevels.ExtraKer
import Formalism.SharpRestriction.InertJacobiLevels.ExtraVal
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

structure PlEmb (D : D7) where
  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_spec : ∀ w x, ∃ hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ, iL w x = lam w ⟨D.what₂.embLL x, hx⟩
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

def plEmb (D : D7) : PlEmb D where
  lam := fun w => (Examples₂.exists_placeEmb D w).choose
  iL := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose
  iL_spec := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose_spec.1
  iL_int := fun w => (Examples₂.exists_placeEmb D w).choose_spec.choose_spec.2

end Formalism.MainNotions.Inhab

end
