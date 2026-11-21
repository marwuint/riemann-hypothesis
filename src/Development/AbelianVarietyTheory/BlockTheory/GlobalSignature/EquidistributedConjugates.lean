import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def ContainsData (D : D7) (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) : Prop :=
  (∀ x : D.host.K, D.host.φ₀ (x : D.host.E) ∈ M) ∧ g2 Λ ∈ M ∧ g3 Λ ∈ M

def FixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Prop :=
  ∀ (x : D.host.K) (y : M), (y : ℂ) = D.host.φ₀ (x : D.host.E) → ρ y = (y : ℂ)

def conjEmb (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : M →ₐ[ℚ] ℂ :=
  ((Complex.conjAe : ℂ →ₐ[ℝ] ℂ).restrictScalars ℚ).comp ρ

theorem conjEmb_apply (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (y : M) :
    conjEmb M ρ y = (starRingEnd ℂ) (ρ y) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates
