import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAway

variable {p : ℕ} [Fact p.Prime]

def incl (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    R ⊗[ℚ] algF P →ₐ[R] R ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id R R) ((algF P).val.restrictScalars ℚ)

theorem incl_tmul (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (a : R) (m : algF P) :
    incl R P (a ⊗ₜ m) = a ⊗ₜ (m : G.C) := rfl

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

end GlobalTheory.CentAway
