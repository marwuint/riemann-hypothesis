import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps

noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct

namespace GlobalTheory.DetInv

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

scoped instance algA : Algebra ℤ_[p] (Ainf p O) := (ofPadic p O).toAlgebra

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

abbrev RL : Type := Ainf p O ⊗[ℤ_[p]] Λ

variable {p O Λ}

abbrev inA (a : Ainf p O) : RL p O Λ := algebraMap (Ainf p O) (RL p O Λ) a

abbrev rhoTA {ε : PreTilt O p} {h : ℕ} (D : Datum ε h Λ) (l : Λ) :
    Matrix (Fin h) (Fin h) (Ainf p O) := (D.ρT l).map (ofPadic p O)

end GlobalTheory.DetInv
