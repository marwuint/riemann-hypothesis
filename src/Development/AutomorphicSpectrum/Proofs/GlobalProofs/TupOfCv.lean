import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TraceGramDetNeZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteComponentCoordinatesAction

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth

section Gen
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

def chiG (G : Matrix ι ι F) (u v : ι → 𝔸[F]) : ℂ :=
  (adelicChar F (u ⬝ᵥ (G.map (algebraMap F 𝔸[F]) *ᵥ v)) : ℂ)

end Gen

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
