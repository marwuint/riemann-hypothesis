import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds

noncomputable section

namespace PI.DvRows

namespace GramDeterminantPositive

open Matrix
open scoped ComplexOrder

section NF

open NumberField Formalism.BasicNotions PI.Dv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def rho (φ : K →+* ℂ) : K →+* ℂ := (starRingEnd ℂ).comp (φ.comp (starRingEnd K))

lemma rho_apply (φ : K →+* ℂ) (x : K) : rho φ x = star (φ (star x)) := rfl

variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)

end NF

end GramDeterminantPositive

open NumberField Formalism.BasicNotions PI.Dv GramDeterminantPositive Matrix

end PI.DvRows
