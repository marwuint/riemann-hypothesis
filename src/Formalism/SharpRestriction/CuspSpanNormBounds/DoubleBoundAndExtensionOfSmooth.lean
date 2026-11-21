import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Side

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def FI (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (u v : H) : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

end Side

end Formalism.MainNotions.DoubleDerivativeSmoothness
