import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatSumCmp

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt latM_eq_dual eisClass_mk latPt_ne_zero)

section Pairs

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def vPt (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (p : FR E × FR E) : Fin (Module.finrank ℚ (FR E)) → ℂ :=
  fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j p.1 : ℂ) + (e j p.2 : ℂ) * τ (e j)))

theorem vPt_apply (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (p : FR E × FR E) (j : Fin (Module.finrank ℚ (FR E))) :
    vPt e τ lam p j = lam j * latPt τ p (e j) := rfl

end Pairs

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

end GlobalTheory.LatSumCmp
