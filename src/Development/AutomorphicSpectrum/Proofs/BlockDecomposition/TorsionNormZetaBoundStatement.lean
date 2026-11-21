import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumCompBoundedFibresLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationProperties

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_norm_zeta_bound : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ r : ℝ, 1 < r → Summable (fun x : (Fin m → K) ⧸ L => (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' x : (Fin m → K) ⧸ L, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) ≤ zetaR K r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion <;> assumption)
