import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionSumZetaBoundDelta
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockQuotientInjection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_sum_zeta_bound_delta : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (r : ℝ), 1 < r → Summable (fun U : (Fin m → E) ⧸ intVec E m => (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' U : (Fin m → E) ⧸ intVec E m, (Ideal.absNorm (tor c (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) ≤ delta c * zetaR E r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor <;> assumption)
