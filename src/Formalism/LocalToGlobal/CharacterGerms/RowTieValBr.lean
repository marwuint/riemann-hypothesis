import Formalism.LocalToGlobal.CharacterGerms.ValueEquationOfProjectors

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def EndoLogSt (Y : FBChart C V O dd) : Prop :=
  ∀ ε : Pt C 1 dd, (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)) →
    ∀ (τ : Type) [Finite τ] (a : Fin dd → MvPowerSeries τ C), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => VP.exAt Y a q.2) (ε i) =
      VP.exAt Y (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • a j) i

end Formalism.L2.FormalSeriesBounds
