import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem interp_rho (m₀ m₁ : ConeMetric ℂ (Ix κ)) (t : ℝ) (z : Ix κ → ℂ) :
    (interp m₀ m₁ t).ρ z = m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t := rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
