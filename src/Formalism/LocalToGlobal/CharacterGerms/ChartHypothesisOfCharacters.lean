import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffPderivUncurry
import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

open VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem integralSeries_uncurry_one {χ : PS C 1 dd} (h : IntS V χ) : IntS V (un1 χ) := by
  intro μ
  exact h _

end ChG

end Formalism.L2.FormalSeriesBounds
