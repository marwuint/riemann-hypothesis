import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def PtsLocalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g g' : ((Σ k, ι k) → ℂ) → ℝ),
    (∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z) → (∀ z ∈ mcPts P, g z = g' z) →
    ptsIntegralAt P Ψ φ g = ptsIntegralAt P Ψ φ' g' ∧ ptsIntegral P φ g = ptsIntegral P φ' g'

end ReciprocityTheory.ChartRestriction.G.Geo
