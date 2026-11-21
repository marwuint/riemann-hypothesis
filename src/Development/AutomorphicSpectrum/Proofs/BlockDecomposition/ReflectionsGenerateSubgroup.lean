import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.PairList

open Matrix

variable {R : Type} [CommRing R] {M : ℕ}

def wv (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) : Fin M → R :=
  fun j => ∑ i, c (a i) * Jm i j

theorem qr_eq (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    qr c Jm a k = 1 + k • vecMulVec a (wv c Jm a) := rfl

end GlobalTheory.CompanionTheory.SaGen.PairList
