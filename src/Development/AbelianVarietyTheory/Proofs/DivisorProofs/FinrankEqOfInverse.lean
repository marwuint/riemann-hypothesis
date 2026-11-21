import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PartShift

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

section Data

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

theorem map_ofPadic_theta {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℤ_[p]) :
    (X.map (ofPadic p O)).map (WittVector.fontaineTheta O p) = X.map (padicToO p O) := rfl

end Data

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv

end GlobalTheory.DetInv
