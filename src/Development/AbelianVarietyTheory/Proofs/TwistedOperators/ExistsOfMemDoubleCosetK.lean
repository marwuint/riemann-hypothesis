import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LatticeCosetUniformizer

namespace GlobalTheory.MinusculeCosetsProof

open Matrix IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.LatticeCosetUniformizer

section General

variable {O F : Type} [CommRing O] [Field F] [Algebra O F] {n : ℕ}

def intLattice (F : Type) [Field F] [Algebra O F] (A : Matrix (Fin n) (Fin n) O) :
    Submodule O (Fin n → F) :=
  LinearMap.range ((inclVec O F n).comp A.mulVecLin)

theorem mem_intLattice (A : Matrix (Fin n) (Fin n) O) (x : Fin n → F) :
    x ∈ intLattice F A ↔ ∃ v, inclVec O F n (A *ᵥ v) = x := Iff.rfl

theorem inclVec_apply (v : Fin n → O) (i : Fin n) : inclVec O F n v i = algebraMap O F (v i) := rfl

theorem mem_scaleBy (a : O) (L : Submodule O (Fin n → F)) (x : Fin n → F) :
    x ∈ scaleBy O a L ↔ ∃ y ∈ L, a • y = x := Iff.rfl

variable [IsLocalRing O]

end General

end GlobalTheory.MinusculeCosetsProof
