import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.PutNest

theorem put_apply' {R : Type} [CommRing R] (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (i j : Fin n) :
    put n o₁ o₂ X i j = if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
      X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

end GlobalTheory.GamMul.PutNest
