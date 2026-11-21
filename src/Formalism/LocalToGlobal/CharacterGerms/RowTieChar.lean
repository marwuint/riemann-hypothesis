import Formalism.LocalToGlobal.CharacterGerms.RowTieTop

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def FBChart.IsChar (Y : FBChart C V O dd) (χ : PS C 1 dd) : Prop :=
  IntS V χ ∧ MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] χ = ev (n := 2) ![pt C dd 0] χ * ev (n := 2) ![pt C dd 1] χ

def dlogC (χ : PS C 1 dd) (i : Fin dd) : C := MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) χ

end Formalism.L2.FormalSeriesBounds
