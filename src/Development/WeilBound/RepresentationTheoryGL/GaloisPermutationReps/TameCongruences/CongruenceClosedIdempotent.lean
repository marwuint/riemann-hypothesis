import Mathlib

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.DzCong

structure Fam (G : Type) {X I : Type} [Group G] [MulAction G X] [Fintype X] (T : I → Matrix X X ℤ) : Prop where
  comm : ∀ i j, T i * T j = T j * T i
  equi : ∀ i (g : G) x y, T i (g • x) (g • y) = T i x y

end PositivityTheory.Rg.DzCong

end
