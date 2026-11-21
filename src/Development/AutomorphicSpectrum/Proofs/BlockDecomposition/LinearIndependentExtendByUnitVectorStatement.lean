import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_extend_by_unit_vector : ∀ (K : Type) [CommRing K] (M n : ℕ) (α : K), IsUnit α → ∀ (c : Fin n → K) (X : Fin n → Fin M → K), LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff
