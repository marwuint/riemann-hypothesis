import Formalism.LocalToGlobal.CharacterGerms.RowTieValL

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def IsIU (V : VF C) {σ : Type} (U : MvPowerSeries σ C) : Prop :=
  IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0

theorem IsIU.one {σ : Type} : IsIU V (1 : MvPowerSeries σ C) := by
  refine ⟨fun μ => ?_, ?_⟩
  · unfold VF.Ge
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · rw [AddValuation.map_one]; exact le_rfl
    · rw [AddValuation.map_zero]; exact le_top
  · rw [map_one, AddValuation.map_one]

theorem IsIU.mul {σ : Type} {U U' : MvPowerSeries σ C} (h : IsIU V U) (h' : IsIU V U') : IsIU V (U * U') :=
  ⟨IntS.mul h.1 h'.1, by rw [map_mul, AddValuation.map_mul, h.2, h'.2, add_zero]⟩

theorem IsIU.prod {σ ι : Type} (s : Finset ι) {U : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IsIU V (U i)) :
    IsIU V (∏ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact IsIU.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

structure IsProj (π : Orb → Fin 2 → Fin dd → PS C 1 dd) : Prop where
  int : ∀ o g i, IntS V (π o g i)
  cc : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0
  pull : ∀ o g i, pull1 Y p (π o g i) = toAllS o ((Y.raw (p o)).expPt g i)

end Defs

end Formalism.L2.FormalSeriesBounds
