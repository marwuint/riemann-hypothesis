import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerToL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def co (p : Bool × Fin n × Fin n) : Mat n →L[ℝ] ℝ :=
  (if p.1 then Complex.reCLM else Complex.imCLM).comp
    (LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℂ p.2.1 p.2.2 : Mat n →ₗ[ℝ] ℂ)))

end GlobalTheory.CompanionTheory.WaveCp.Rep
