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

def ptNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) (z : ι → C) : ℝ :=
  ‖eval z (map σ f)‖ / m.ρ z ^ d

def supNormOn {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) : ℝ :=
  sSup (ptNormOn m σ d f '' S)

theorem conePts_ne_zero (σ : o →+* C) (I : Ideal (MvPolynomial ι o)) :
    ∀ z ∈ conePts σ I, z ≠ 0 :=
  fun _ hz => hz.1

theorem ptNormOn_restrict (m : ConeMetric C ι) (S : Set (ι → C)) (hS : ∀ z ∈ S, z ≠ 0)
    (σ : o →+* C) (d : ℕ) (f : MvPolynomial ι o) (z : ι → C) :
    ptNormOn (m.restrict S hS) σ d f z = ptNorm m σ d f z :=
  rfl

theorem supNormOn_restrict (m : ConeMetric C ι) (σ : o →+* C) (I : Ideal (MvPolynomial ι o))
    (d : ℕ) (f : MvPolynomial ι o) :
    supNormOn (m.restrict (conePts σ I) (conePts_ne_zero σ I)) σ d f = supNorm m σ I d f :=
  rfl

end On

end ReciprocityTheory.ChartRestriction.G.Geo
