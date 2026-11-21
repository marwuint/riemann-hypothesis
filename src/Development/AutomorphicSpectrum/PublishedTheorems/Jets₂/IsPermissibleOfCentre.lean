import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace HCSS

variable {n : ℕ}

def lieOf (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end HCSS

namespace HCSS

end HCSS

end GlobalTheory.CompanionTheory.Hypotheses₂

end
