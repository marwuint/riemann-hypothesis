import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings

structure IsPerfectPairing {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]
    (e : A → B → Kˣ) : Prop where
  add_left : ∀ a a' t, e (a + a') t = e a t * e a' t
  add_right : ∀ a t t', e a (t + t') = e a t * e a t'
  nondeg_left : ∀ a, (∀ t, e a t = 1) → a = 0
  nondeg_right : ∀ t, (∀ a, e a t = 1) → t = 0

end GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
