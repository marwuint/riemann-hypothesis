import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.NearPair

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

def rowV (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) : Fin M → R :=
  fun j => ∑ i, c (a i) * Jm i j

theorem qr_eq (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    qr c Jm a k = 1 + k • Matrix.vecMulVec a (rowV c Jm a) := rfl

end Ring

end GlobalTheory.CompanionTheory.SaGen.NearPair
