import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section On

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}

variable (C ι) in

structure ConeMetricOn (S : Set (ι → C)) where

  ρ : (ι → C) → ℝ
  pos : ∀ z ∈ S, 0 < ρ z
  smul : ∀ (c : C) (z : ι → C), z ∈ S → c • z ∈ S → ρ (c • z) = ‖c‖ * ρ z

def ConeMetric.restrict (m : ConeMetric C ι) (S : Set (ι → C)) (hS : ∀ z ∈ S, z ≠ 0) :
    ConeMetricOn C ι S where
  ρ := m.ρ
  pos z hz := m.pos z (hS z hz)
  smul c z _ _ := m.smul c z

end On

end ReciprocityTheory.ChartRestriction.G.Geo
