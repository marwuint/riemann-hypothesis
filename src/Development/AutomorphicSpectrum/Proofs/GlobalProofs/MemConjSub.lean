import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex

variable {F : Type} [Field F]

def Lvl {n : ℕ} (O : Subring F) (c : F) (X : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, ∃ o ∈ O, X a b = c * o

theorem Lvl.add {n : ℕ} {O : Subring F} {c : F} {X Y : Matrix (Fin n) (Fin n) F} (hX : Lvl O c X)
    (hY : Lvl O c Y) : Lvl O c (X + Y) := fun a b => by
  obtain ⟨o, ho, h⟩ := hX a b
  obtain ⟨o', ho', h'⟩ := hY a b
  exact ⟨o + o', O.add_mem ho ho', by simp [h, h', mul_add]⟩

end GlobalTheory.CompanionTheory.QL.QIndex
