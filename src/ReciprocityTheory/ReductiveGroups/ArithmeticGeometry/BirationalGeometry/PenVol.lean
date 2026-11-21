import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter

section Vol

variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}

def smallSectionCount (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : ℝ :=
  Real.log (Nat.card {s : La τ // P τ (s : Ω)})

def arVolP (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) : ℝ :=
  limsup (fun k : ℕ => smallSectionCount P La (a * k) /
    (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop

end Vol

end ReciprocityTheory.ChartRestriction.G.Geo
