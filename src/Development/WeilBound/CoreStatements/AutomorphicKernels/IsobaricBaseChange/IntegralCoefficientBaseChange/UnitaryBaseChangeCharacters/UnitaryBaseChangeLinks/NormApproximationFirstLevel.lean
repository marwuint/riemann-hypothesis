import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormApproximationFirstLevel
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj

open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_approximation_first_level : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), P.1.Separable → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P 1 := by
  exact @GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one
