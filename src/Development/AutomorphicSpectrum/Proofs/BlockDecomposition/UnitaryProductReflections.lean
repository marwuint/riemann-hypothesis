import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.CompanionTheory.SaGen.ReflList

open Formalism.UG (hform UJ cT)

variable {R : Type} [CommRing R] {M : ℕ} (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R)

def rowV (a : Fin M → R) : Fin M → R := fun j => ∑ i, c (a i) * Jm i j

theorem qr_eq (a : Fin M → R) (k : R) : qr c Jm a k = 1 + k • Matrix.vecMulVec a (rowV c Jm a) := rfl

end GlobalTheory.CompanionTheory.SaGen.ReflList
