import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrivLevel

theorem level_dvd_badN (D : D7) {p : ℕ} (hp : p ∈ D.host.levelPrimes) : p ∣ badN D :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) _

theorem badN_pos_iff (D : D7) : 0 < badN D ↔ 0 ∉ D.host.levelPrimes := by
  have h := D.host.qd_big
  constructor
  · intro hb h0
    exact hb.ne' (Nat.eq_zero_of_zero_dvd (level_dvd_badN D h0))
  · intro h0
    unfold badN
    refine Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega)) (Finset.prod_pos fun p hp => ?_)
    exact Nat.pos_of_ne_zero fun e => h0 (e ▸ hp)

end GlobalTheory.TrivLevel
