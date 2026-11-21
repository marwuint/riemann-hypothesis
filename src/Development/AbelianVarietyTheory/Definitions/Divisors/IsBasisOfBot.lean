import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.DetInv

def incl {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C] (h : ℕ) :
    (Fin h → O) →ₗ[O] (Fin h → C) := (Algebra.linearMap O C).compLeft (Fin h)

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

end GlobalTheory.DetInv
