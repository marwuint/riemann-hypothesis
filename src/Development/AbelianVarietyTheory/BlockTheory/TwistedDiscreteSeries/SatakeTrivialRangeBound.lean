import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound

def InTrivialRange (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) : Prop :=
  ∀ i, (q : ℝ) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ (q : ℝ) ^ (((n : ℝ) - 1) / 2)

def SatakeTrivialBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (α : Fin n → ℂˣ),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsSpherical π → HasSatake π α →
      InTrivialRange (resCard k) α

section Basic₂

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound
