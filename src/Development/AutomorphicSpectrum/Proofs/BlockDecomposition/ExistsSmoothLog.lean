import Formalism.UnipotentAdelicQuotients.SmComplete
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace GlobalTheory.CompanionTheory.SmoothLog

def OpMat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

instance (n : ℕ) : NormedRing (OpMat n) := Matrix.linftyOpNormedRing
instance (n : ℕ) : NormedAlgebra ℝ (OpMat n) := Matrix.linftyOpNormedAlgebra
instance (n : ℕ) : FiniteDimensional ℝ (OpMat n) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
instance (n : ℕ) : CompleteSpace (OpMat n) := FiniteDimensional.complete ℝ _

end GlobalTheory.CompanionTheory.SmoothLog
