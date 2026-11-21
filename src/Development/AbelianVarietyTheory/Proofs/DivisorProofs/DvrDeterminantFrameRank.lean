import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] {C : Type} [Field C] [Algebra O C]

theorem incl_apply' (h : ℕ) (l : Fin h → O) : incl C h l = fun i => algebraMap O C (l i) := rfl

end SlopeTestRemainingChoices

end GlobalTheory.DetInv
