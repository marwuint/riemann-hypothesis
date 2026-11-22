import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlRelationsOnKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjoint
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.GelfandCentralHolds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.GKLie
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Hypotheses₂

end GlobalTheory.CompanionTheory.Hypotheses₂

namespace GlobalTheory.CompanionTheory.Hypotheses₂

section Words

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def wordE (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (l : List (Matrix (Fin n) (Fin n) ℂ)) : Module.End ℂ M :=
  (l.map A).prod

@[simp] theorem wordE_nil (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) : wordE A [] = 1 := rfl

@[simp] theorem wordE_cons (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (Z : Matrix (Fin n) (Fin n) ℂ)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : wordE A (Z :: l) = A Z * wordE A l := by
  simp [wordE]

end Words

end GlobalTheory.CompanionTheory.Hypotheses₂

end
