import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix

namespace GlobalTheory.FrameModel

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

def embVal (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) :
    (Λ →+* O) → v.valuationSubring :=
  fun σ => ⟨algebraMap O C (σ α), (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩

theorem coe_embVal (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) (σ : Λ →+* O) :
    (embVal v hv α σ : C) = algebraMap O C (σ α) := rfl

end GlobalTheory.FrameModel
